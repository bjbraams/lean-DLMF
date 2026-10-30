/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Mathieu.Modified.Basic.Functions
public import DLMF.Mathieu.Modified.Basic.AsymptoticData
public import DLMF.Mathieu.Modified.Basic.IntegralKernels

/-!
# Modified Mathieu functions: definitions (DLMF §§28.20, 28.22–28.28)

This is the definitions file for the modified Mathieu functions of DLMF §§28.20–28.28.

* `IsModMathieuSolution a q w`: `w` is an entire solution of the modified Mathieu equation
  28.20.1 `w'' - (a - 2q cosh 2z) w = 0`.
* `modMathieuCe ν z q = Ce_ν(z, q)`, `modMathieuSe`, `modMathieuMe`, `modMathieuFe`,
  `modMathieuGe` (28.20.3–28.20.7): Mathieu functions at imaginary argument.
* `besselJExp μ h z`, `besselYExp μ h z`, `mathieuCylExp j μ h z`: the cylinder functions
  `𝒞^{(j)}_μ(h e^z)` of 28.23.1 (`J`, `Y`, `H^{(1)}`, `H^{(2)}`), **continued analytically in
  `z`** from the real axis: `(h e^z / 2)^μ` is read as `(h / 2)^μ e^{μ z}` with the principal
  power of `h / 2`. For `h > 0` and `|Im z| < π` they agree with the principal-branch Bessel
  functions at `h e^z`; elsewhere they are DLMF's continuations (DLMF continues `M^{(j)}_ν`
  analytically in `z`, §28.20(iii)).
* `mathieuCylCosh j μ h z`, `mathieuCylSinh j μ h z`: `𝒞^{(j)}_μ(2h cosh z)` and
  `𝒞^{(j)}_μ(2h sinh z)` continued from the positive real axis through the half-plane
  `Re z > 0`, written as `𝒞^{(j)}_μ(h e^{z'})` with `z' = z + log(1 ± e^{-2z})` (principal
  logarithm; `|e^{-2z}| < 1` there).
* `modMathieuM j ν z h = M^{(j)}_ν(z, h)` (§28.20(iii)), **defined by the absolutely convergent
  series 28.24.1 in cross-products of Bessel functions**,
  `c^ν_{2n}(h²) M^{(j)}_ν(z, h) = ∑_ℓ (-1)^ℓ c^ν_{2ℓ}(h²) J_{ℓ-n}(h e^{-z}) 𝒞^{(j)}_{ν+n+ℓ}(h e^z)`,
  for one index `n = modMathieuIndex ν h` with `c^ν_{2n}(h²) ≠ 0` (chosen by
  `Classical.choose`; the independence of `n` is the theorem 28.24.1). The coefficients are
  ACQ28B's `mathieuMeCoeff ν (h²)`, which for integer `ν` follow 28.12.11.
* `radialMathieuMc j n z h = Mc^{(j)}_n(z, h)`, `radialMathieuMs j n z h = Ms^{(j)}_n(z, h)`
  (28.20.15–28.20.16) and `modMathieuIe`, `modMathieuIo`, `modMathieuKe`, `modMathieuKo`
  (28.20.17–28.20.20).
* The joining factors `g_{e,m}`, `g_{o,m}`, `f_{e,m}`, `f_{o,m}` of 28.22.5–28.22.10, the
  coefficients `D^±_m` of 28.25.2–28.25.3, Goldstein's `Fc_m`, `Gc_m`, `Fs_m`, `Gs_m`
  (28.26.1–28.26.3), the kernels `w`, `R`, `φ` of §28.28, the path integrals along `𝓛_j`
  (28.28.6), the cross-products `D_0`, `D_1`, `Ds_k`, `Dc_k`, `Dsc_k` and the integrals
  `α`, `γ`, `α̂`, `β̂`, `γ̂` of §28.28(iii)–(iv).

## Design notes

* The integer-order functions of `DLMF.Mathieu.Basic` are defined for real `q` only; the
  radial functions take a complex `h` and use `q = h²`, so for integer order they are
  meaningful when `h²` is real (`h` real or purely imaginary, as in `Ie_n`, `Ke_n`).
* For the general order the definition by 28.24.1 avoids the asymptotic characterization of
  §28.20(iii) (stated as theorems). For integer `ν = n` the series reduces to
  28.24.2–28.24.5 (checked numerically); for `ν = -n` some coefficients vanish
  (e.g. `c^{-2}_0 = 0`), which is why the index `n` is chosen with `c^ν_{2n} ≠ 0`.
* `j ∈ {1, 2, 3, 4}`; other values of `j` give the junk value `0`.
-/
