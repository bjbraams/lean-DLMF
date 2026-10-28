/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Weierstrass.Relations.ThetaIdentities
public import DLMF.Weierstrass.Relations.JacobiIdentities

/-!
# Relations to theta and Jacobian elliptic functions (DLMF §23.6)

Theta functions are the project's lattice-parameter forms `θⱼ(z|τ)`
(`DLMF.Elliptic.jacobiThetaOneTau … jacobiThetaFourTau`), which are DLMF's `θⱼ(z, q)` with
`q = e^{iπτ}`; using `τ = ω₃/ω₁` directly avoids the branch of `q^{1/4}` (which is written
`e^{iπτ/4}` below). Derivatives at `0` are Lean derivatives in `z`
(`DLMF.Theta.jacobiThetaOneDerivNullTau`, `iteratedDeriv 3`), and `d/dz ln θ₁` is the
logarithmic derivative `θ₁'/θ₁`.

**Jacobian functions (§23.6(ii)).** DLMF states 23.6.16–23.6.26 for *any* pair of generators
with `K = K(k)` the complete elliptic integral of the modulus. The squared quantities in
23.6.17 hold for every pair of generators only if `K` denotes the lattice quarter period
`K = (π/2)θ₃²(0|τ)` (`DLMF.JacobiElliptic.compEllIntKTau`), not the principal integral of
`k = θ₂²/θ₃²`: `k²` is invariant under `τ ↦ τ/(2τ + 1)` while `ω₁²(e₁ - e₃)` is not
(numerical check: `ω₁ = 1.1 + 0.2i`, `ω₃ = 0.3 + 0.9i`, generators `(ω₁ + 2ω₃, ω₃)` give
`K(k)² - ω₁²(e₁ - e₃) ≈ 11.0 - 13.7i`). The lattice forms are therefore acquired for all
generators, and the literal principal form under the hypothesis `τ = iK'(k)/K(k)`.

**Source correction.** In 23.6.29 the last term has the wrong sign: the correct identity is
`ζ(z|𝕃₃) - ζ(z + 2iK'|𝕃₃) + ζ(2iK'|𝕃₃) = cs(z, k)` (the printed `- ζ(2iK'|𝕃₃)` fails
numerically, e.g. by `-0.49i` for `k² = 0.3`, `z = 0.37 + 0.21i`; the corrected form agrees to
`10⁻¹⁰`). The correction also follows from the oddness of `cs` and `ζ` and 23.2.11.
-/
