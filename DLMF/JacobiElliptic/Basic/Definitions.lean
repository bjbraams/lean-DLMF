/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Theta.Defs

/-!
# Theta-quotient definitions of Jacobian elliptic functions

Glaisher letters, normalized theta quotients, lattice parameters and the twelve Jacobian
elliptic functions.

Source references and common attribution are retained in
`DLMF.JacobiElliptic.Basic`.
-/

@[expose] public section

open Complex DLMF.Elliptic

open scoped Real

noncomputable section

namespace DLMF.JacobiElliptic

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

end DLMF.JacobiElliptic
end
end
