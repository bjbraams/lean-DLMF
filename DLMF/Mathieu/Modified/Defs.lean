/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic
public import DLMF.Mathieu.Noninteger.Defs
public import DLMF.Bessel.Basic

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

@[expose] public noncomputable section

open Complex Set Filter MeasureTheory
open scoped Topology Real Classical

namespace DLMF.Mathieu

/-! ### The modified Mathieu equation (§28.20(i)) -/

/-- The **modified Mathieu equation** (DLMF 28.20.1) `w'' - (a - 2q cosh 2z) w = 0`, complex
`a`, `q`, `z`: `w` is entire and its derivative has derivative `(a - 2q cosh 2z) w(z)`. -/
@[dlmf 28.20.E1]
structure IsModMathieuSolution (a q : ℂ) (w : ℂ → ℂ) : Prop where
  /-- Solutions are entire. -/
  differentiable : Differentiable ℂ w
  /-- The equation `w'' = (a - 2q cosh 2z) w`. -/
  hasDerivAt_deriv : ∀ z, HasDerivAt (deriv w) ((a - 2 * q * Complex.cosh (2 * z)) * w z) z

/-! ### `Ce_ν`, `Se_ν`, `Me_ν`, `Fe_n`, `Ge_n` (§28.20(ii)) -/

/-- The **modified Mathieu function** `Ce_ν(z, q) = ce_ν(± i z, q)` (DLMF 28.20.3),
`ν ≠ -1, -2, …`. For `ν = n ∈ ℕ` this is `ce_n(iz, q)` (real `q`; junk `0` for nonreal `q`);
otherwise `ce_ν(iz, q)` of 28.12.12. -/
@[dlmf 28.20.E3]
def modMathieuCe (ν z q : ℂ) : ℂ :=
  if h : ∃ n : ℕ, (n : ℂ) = ν then
    (if q.im = 0 then mathieuCe h.choose (I * z) q.re else 0)
  else mathieuCeNu ν (I * z) q

/-- The **modified Mathieu function** `Se_ν(z, q) = ∓ i se_ν(± i z, q)` (DLMF 28.20.4),
`ν ≠ 0, -1, -2, …` (upper sign; both signs agree since `se_ν` is odd). For `ν = n ≥ 1` this is
`-i se_n(iz, q)` (real `q`; junk `0` for nonreal `q`); otherwise `-i se_ν(iz, q)` of 28.12.13. -/
@[dlmf 28.20.E4]
def modMathieuSe (ν z q : ℂ) : ℂ :=
  if h : ∃ n : ℕ, n ≠ 0 ∧ (n : ℂ) = ν then
    (if q.im = 0 then -I * mathieuSe h.choose (I * z) q.re else 0)
  else -I * mathieuSeNu ν (I * z) q

/-- The **modified Mathieu function** `Me_ν(z, q) = me_ν(-iz, q)` (DLMF 28.20.5). -/
@[dlmf 28.20.E5]
def modMathieuMe (ν z q : ℂ) : ℂ :=
  mathieuMe ν (-I * z) q

/-- The **modified Mathieu function** `Fe_n(z, q) = ∓ i fe_n(± i z, q)` (DLMF 28.20.6),
`n = 0, 1, …`, real `q` (upper sign; `fe_n` is odd). -/
@[dlmf 28.20.E6]
def modMathieuFe (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  -I * mathieuFe n (I * z) q

/-- The **modified Mathieu function** `Ge_n(z, q) = ge_n(± i z, q)` (DLMF 28.20.7),
`n = 1, 2, …`, real `q` (`ge_n` is even). -/
@[dlmf 28.20.E7]
def modMathieuGe (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  mathieuGe n (I * z) q

/-! ### Cylinder functions continued in `z` (28.23.1) -/

/-- `J_μ(h e^z)` **continued analytically in `z`**: `(h/2)^μ e^{μz} ₀F̃₁(; μ+1; -(h e^z)²/4)`
(DLMF 10.2.2 with `(h e^z / 2)^μ` read as `(h/2)^μ e^{μ z}`, principal power of `h/2`). Entire
in `z`; for `h > 0` and `|Im z| < π` it is the principal-branch `J_μ(h e^z)`. -/
def besselJExp (μ h z : ℂ) : ℂ :=
  (h / 2) ^ μ * Complex.exp (μ * z) *
    regularizedHGFun (∅ : Multiset ℂ) {μ + 1} (-((h * Complex.exp z) ^ 2 / 4))

/-- `Y_μ(h e^z)` continued analytically in `z` (DLMF 10.2.3, integer orders by the limit in the
order, as for `DLMF.Bessel.besselY`), built from `besselJExp`. -/
def besselYExp (μ h z : ℂ) : ℂ :=
  if ∃ k : ℤ, μ = k then
    Filter.limUnder (𝓝[≠] μ) (fun μ' =>
      (besselJExp μ' h z * Complex.cos (μ' * π) - besselJExp (-μ') h z) / Complex.sin (μ' * π))
  else (besselJExp μ h z * Complex.cos (μ * π) - besselJExp (-μ) h z) / Complex.sin (μ * π)

/-- The **cylinder functions** `𝒞^{(j)}_μ(h e^z)` of DLMF 28.23.1, continued analytically in
`z`: `j = 1, 2, 3, 4` give `J_μ`, `Y_μ`, `H^{(1)}_μ = J_μ + i Y_μ`, `H^{(2)}_μ = J_μ - i Y_μ`
(DLMF 10.4.3); junk `0` for other `j`. -/
@[dlmf 28.23.E1]
def mathieuCylExp (j : ℕ) (μ h z : ℂ) : ℂ :=
  match j with
  | 1 => besselJExp μ h z
  | 2 => besselYExp μ h z
  | 3 => besselJExp μ h z + I * besselYExp μ h z
  | 4 => besselJExp μ h z - I * besselYExp μ h z
  | _ => 0

/-- The principal-branch cylinder functions `𝒞^{(j)}_μ(w)` of DLMF 28.23.1 (`J_μ`, `Y_μ`,
`H^{(1)}_μ`, `H^{(2)}_μ` at `w`, with `DLMF.Bessel.besselY`); junk `0` for other `j`. -/
@[dlmf 28.23.E1]
def mathieuCyl (j : ℕ) (μ w : ℂ) : ℂ :=
  match j with
  | 1 => besselJ μ w
  | 2 => DLMF.Bessel.besselY μ w
  | 3 => besselJ μ w + I * DLMF.Bessel.besselY μ w
  | 4 => besselJ μ w - I * DLMF.Bessel.besselY μ w
  | _ => 0

/-- `𝒞^{(j)}_μ(2h cosh z)` continued from the positive real axis through `Re z > 0`
(DLMF 28.23.2, 28.23.6): `𝒞^{(j)}_μ(h e^{z'})` with `z' = z + log(1 + e^{-2z})`, so that
`h e^{z'} = 2h cosh z`. Meaningful for `Re z > 0`. -/
def mathieuCylCosh (j : ℕ) (μ h z : ℂ) : ℂ :=
  mathieuCylExp j μ h (z + Complex.log (1 + Complex.exp (-2 * z)))

/-- `𝒞^{(j)}_μ(2h sinh z)` continued from the positive real axis through `Re z > 0`
(DLMF 28.23.4, 28.23.7): `𝒞^{(j)}_μ(h e^{z'})` with `z' = z + log(1 - e^{-2z})`. -/
def mathieuCylSinh (j : ℕ) (μ h z : ℂ) : ℂ :=
  mathieuCylExp j μ h (z + Complex.log (1 - Complex.exp (-2 * z)))

/-! ### The functions `M^{(j)}_ν` (§28.20(iii), 28.24.1) -/

/-- The parameters `(ν, h)` for which `c^ν_{2m}(h²)` (`mathieuMeCoeff ν (h²)`) are DLMF's
coefficients: `ν ∉ ℤ` with `h²` normal along the segment `[0, h²]` (ACQ28B's
`MathieuNormalSegment`, which holds for real `ν ∉ ℤ` and real `h²`), or `ν ∈ ℤ` with `h²`
real (the integer-order functions are defined for real `q`). -/
def ModMathieuAdmissible (ν h : ℂ) : Prop :=
  ((∀ m : ℤ, (m : ℂ) ≠ ν) ∧ MathieuNormalSegment ν (h ^ 2)) ∨
    ((∃ m : ℤ, (m : ℂ) = ν) ∧ (h ^ 2).im = 0)

/-- The `ℓ`-th term `(-1)^ℓ c^ν_{2ℓ}(h²) J_{ℓ-n}(h e^{-z}) 𝒞^{(j)}_{ν+n+ℓ}(h e^z)` of the
cross-product series DLMF 28.24.1 with index `n`. -/
def modMathieuTerm (j : ℕ) (ν z h : ℂ) (n ℓ : ℤ) : ℂ :=
  (-1 : ℂ) ^ ℓ * mathieuMeCoeff ν (h ^ 2) ℓ * besselJExp ((ℓ - n : ℤ) : ℂ) h (-z) *
    mathieuCylExp j (ν + n + ℓ) h z

/-- An index `n` with `c^ν_{2n}(h²) ≠ 0` (by choice; `0` if all coefficients vanish), used to
normalize 28.24.1. DLMF 28.22.13 recommends, for computation, an index of maximal
`|c^ν_{2n}(h²)|`; by 28.24.1 the value of `M^{(j)}_ν` does not depend on the index. -/
def modMathieuIndex (ν h : ℂ) : ℤ :=
  if hc : ∃ n : ℤ, mathieuMeCoeff ν (h ^ 2) n ≠ 0 then hc.choose else 0

/-- The **modified Mathieu functions** `M^{(j)}_ν(z, h)`, `j = 1, 2, 3, 4` (DLMF §28.20(iii)),
`q = h²`, `a = λ_ν(q)`, defined by the cross-product series 28.24.1:
`M^{(j)}_ν(z, h) = c^ν_{2n}(h²)⁻¹ ∑_ℓ (-1)^ℓ c^ν_{2ℓ}(h²) J_{ℓ-n}(h e^{-z}) 𝒞^{(j)}_{ν+n+ℓ}(h e^z)`
with `n = modMathieuIndex ν h`; the Bessel functions are continued analytically in `z`
(`besselJExp`, `mathieuCylExp`), so `M^{(j)}_ν` is DLMF's function on the whole `z`-plane. The
characterization of §28.20(iii) (solutions of 28.20.1 with the asymptotics 28.20.9–28.20.12)
is stated as theorems. -/
@[dlmf 28.20.iii]
def modMathieuM (j : ℕ) (ν z h : ℂ) : ℂ :=
  (mathieuMeCoeff ν (h ^ 2) (modMathieuIndex ν h))⁻¹ *
    ∑' ℓ : ℤ, modMathieuTerm j ν z h (modMathieuIndex ν h) ℓ

/-- The **radial Mathieu function** `Mc^{(j)}_n(z, h) = M^{(j)}_n(z, h)`, `n = 0, 1, …`
(DLMF 28.20.15). -/
@[dlmf 28.20.E15]
def radialMathieuMc (j n : ℕ) (z h : ℂ) : ℂ :=
  modMathieuM j n z h

/-- The **radial Mathieu function** `Ms^{(j)}_n(z, h) = (-1)^n M^{(j)}_{-n}(z, h)`,
`n = 1, 2, …` (DLMF 28.20.16). -/
@[dlmf 28.20.E16]
def radialMathieuMs (j n : ℕ) (z h : ℂ) : ℂ :=
  (-1 : ℂ) ^ n * modMathieuM j (-(n : ℂ)) z h

/-! ### `Ie_n`, `Io_n`, `Ke_n`, `Ko_n` (§28.20(v)) -/

/-- `Ie_n(z, h) = i^{-n} Mc^{(1)}_n(z, ih)` (DLMF 28.20.17). -/
@[dlmf 28.20.E17]
def modMathieuIe (n : ℕ) (z h : ℂ) : ℂ :=
  I ^ (-(n : ℤ)) * radialMathieuMc 1 n z (I * h)

/-- `Io_n(z, h) = i^{-n} Ms^{(1)}_n(z, ih)` (DLMF 28.20.18). -/
@[dlmf 28.20.E18]
def modMathieuIo (n : ℕ) (z h : ℂ) : ℂ :=
  I ^ (-(n : ℤ)) * radialMathieuMs 1 n z (I * h)

/-- `Ke_n(z, h)` (DLMF 28.20.19): `Ke_{2m} = (-1)^m (π i / 2) Mc^{(3)}_{2m}(z, ih)` and
`Ke_{2m+1} = (-1)^{m+1} (π / 2) Mc^{(3)}_{2m+1}(z, ih)`. -/
@[dlmf 28.20.E19]
def modMathieuKe (n : ℕ) (z h : ℂ) : ℂ :=
  if Even n then (-1 : ℂ) ^ (n / 2) * (π * I / 2) * radialMathieuMc 3 n z (I * h)
  else (-1 : ℂ) ^ (n / 2 + 1) * (π / 2) * radialMathieuMc 3 n z (I * h)

/-- `Ko_n(z, h)` (DLMF 28.20.20): `Ko_{2m} = (-1)^m (π i / 2) Ms^{(3)}_{2m}(z, ih)` and
`Ko_{2m+1} = (-1)^{m+1} (π / 2) Ms^{(3)}_{2m+1}(z, ih)`. -/
@[dlmf 28.20.E20]
def modMathieuKo (n : ℕ) (z h : ℂ) : ℂ :=
  if Even n then (-1 : ℂ) ^ (n / 2) * (π * I / 2) * radialMathieuMs 3 n z (I * h)
  else (-1 : ℂ) ^ (n / 2 + 1) * (π / 2) * radialMathieuMs 3 n z (I * h)

/-! ### Regions and factors of §§28.20–28.24 -/

/-- The filter `Re z → +∞` with `a ≤ Im z ≤ b`. -/
def m28c_strip (a b : ℝ) : Filter ℂ :=
  comap Complex.re atTop ⊓ 𝓟 {z : ℂ | a ≤ z.im ∧ z.im ≤ b}

/-- The Wronskian `𝒲{f, g}(z) = f(z) g'(z) - f'(z) g(z)` of two functions of `z`
(DLMF 1.13.4), written out. -/
def m28c_wronskian (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * deriv g z - deriv f z * g z

/-- The convergence condition of the integer-order series in `2h cosh z` (DLMF 28.23, after
28.23.13): for `j = 1` all `z` (except the zeros of `cosh z`, where `𝒞(2h cosh z)` is
continued), for `j = 2, 3, 4` the region `Re z > 0`, `|cosh z| > 1`. -/
def ModMathieuCoshRegion (j : ℕ) (z : ℂ) : Prop :=
  (j = 1 ∧ Complex.cosh z ≠ 0) ∨ (0 < z.re ∧ 1 < ‖Complex.cosh z‖)

/-- The convergence condition of the integer-order series in `2h sinh z` (DLMF 28.23, after
28.23.13). -/
def ModMathieuSinhRegion (j : ℕ) (z : ℂ) : Prop :=
  (j = 1 ∧ Complex.sinh z ≠ 0) ∨ (0 < z.re ∧ 1 < ‖Complex.sinh z‖)

/-- The factor `ε_s` of §28.24: `ε_0 = 2`, `ε_s = 1` for `s ≥ 1`. -/
def mathieuEpsilon (s : ℕ) : ℂ :=
  if s = 0 then 2 else 1

/-! ### Joining factors (§28.22(i)) -/

/-- The **joining factor** `g_{e,m}(h)` (DLMF 28.22.5–28.22.6), real `h`:
`g_{e,2m} = (-1)^m √(2/π) ce_{2m}(π/2, h²) / A^{2m}_0(h²)` and
`g_{e,2m+1} = (-1)^{m+1} √(2/π) ce'_{2m+1}(π/2, h²) / (h A^{2m+1}_1(h²))`. -/
@[dlmf 28.22.E5, dlmf 28.22.E6]
def mathieuJoinGe (m : ℕ) (h : ℝ) : ℂ :=
  if Even m then
    (-1 : ℂ) ^ (m / 2) * Real.sqrt (2 / π) * mathieuCe m (π / 2) (h ^ 2) /
      mathieuFourierA m 0 (h ^ 2)
  else
    (-1 : ℂ) ^ (m / 2 + 1) * Real.sqrt (2 / π) *
      deriv (fun z => mathieuCe m z (h ^ 2)) (π / 2) / (h * mathieuFourierA m 1 (h ^ 2))

/-- The **joining factor** `g_{o,m}(h)` (DLMF 28.22.7–28.22.8), real `h`, `m ≥ 1`:
`g_{o,2m+1} = (-1)^m √(2/π) se_{2m+1}(π/2, h²) / (h B^{2m+1}_1(h²))` and
`g_{o,2m+2} = (-1)^{m+1} √(2/π) se'_{2m+2}(π/2, h²) / (h² B^{2m+2}_2(h²))`. -/
@[dlmf 28.22.E7, dlmf 28.22.E8]
def mathieuJoinGo (m : ℕ) (h : ℝ) : ℂ :=
  if Odd m then
    (-1 : ℂ) ^ (m / 2) * Real.sqrt (2 / π) * mathieuSe m (π / 2) (h ^ 2) /
      (h * mathieuFourierB m 1 (h ^ 2))
  else
    (-1 : ℂ) ^ ((m - 2) / 2 + 1) * Real.sqrt (2 / π) *
      deriv (fun z => mathieuSe m z (h ^ 2)) (π / 2) / (h ^ 2 * mathieuFourierB m 2 (h ^ 2))

/-- The **joining factor** `f_{e,m}(h) = -√(π/2) g_{e,m}(h) Mc^{(2)}_m(0, h)` (DLMF 28.22.9). -/
@[dlmf 28.22.E9]
def mathieuJoinFe (m : ℕ) (h : ℝ) : ℂ :=
  -(Real.sqrt (π / 2) : ℂ) * mathieuJoinGe m h * radialMathieuMc 2 m 0 h

/-- The **joining factor** `f_{o,m}(h) = -√(π/2) g_{o,m}(h) Ms^{(2)'}_m(0, h)` (DLMF 28.22.10),
the prime denoting `d/dz`. -/
@[dlmf 28.22.E10]
def mathieuJoinFo (m : ℕ) (h : ℝ) : ℂ :=
  -(Real.sqrt (π / 2) : ℂ) * mathieuJoinGo m h * deriv (fun z => radialMathieuMs 2 m z h) 0

/-! ### Coefficients of the expansion for large `Re z` (§28.25) -/

/-- The pair `(D_{m-1}, D_m)` of the recurrence 28.25.3 with sign `σ = ±1`. -/
def modMathieuAsympDPair (σ a h : ℂ) : ℕ → ℂ × ℂ
  | 0 => (0, 1)
  | m + 1 =>
    let p := modMathieuAsympDPair σ a h m
    (p.2, -((((m : ℂ) + 1 / 2) ^ 2 + σ * ((m : ℂ) + 1 / 4) * (8 * I * h) + 2 * h ^ 2 - a) *
      p.2 + σ * ((m : ℂ) - 1 / 2) * (8 * I * h * m) * p.1) / ((m : ℂ) + 1))

/-- The coefficients `D^±_m` of DLMF 28.25.1, defined by 28.25.2 (`D_{-1} = 0`, `D_0 = 1`) and
the recurrence 28.25.3; `σ = 1` gives `D^+_m` (for `M^{(3)}_ν`), `σ = -1` gives `D^-_m` (for
`M^{(4)}_ν`); `a = λ_ν(h²)`. -/
@[dlmf 28.25.E2, dlmf 28.25.E3]
def modMathieuAsympD (σ a h : ℂ) (m : ℕ) : ℂ :=
  (modMathieuAsympDPair σ a h m).2

/-- The prefactor `e^{±i(2h cosh z - (ν/2 + 1/4)π)} / (π h (cosh z + 1))^{1/2}` of DLMF 28.25.1,
`σ = ±1`; the square root is continued in `z` as `(2πh)^{1/2} cosh(z/2)`. -/
def modMathieuAsympPrefactor (σ ν h z : ℂ) : ℂ :=
  Complex.exp (σ * I * (2 * h * Complex.cosh z - (ν / 2 + 1 / 4) * π)) /
    ((2 * π * h) ^ (1 / 2 : ℂ) * Complex.cosh (z / 2))

/-- The sector filter of DLMF 28.25.4–28.25.5: `Re z → +∞` with
`a ≤ ph h + Im z ≤ b`. -/
def modMathieuAsympFilter (h : ℂ) (a b : ℝ) : Filter ℂ :=
  comap Complex.re atTop ⊓ 𝓟 {z : ℂ | a ≤ Complex.arg h + z.im ∧ Complex.arg h + z.im ≤ b}

/-! ### Goldstein's functions (§28.26(i)) -/

/-- The phase `φ = 2h sinh z - (m + 1/2) arctan(sinh z)` of DLMF 28.26.3 (principal complex
`arctan`, which is analytic for `Re z > 0`, `|Im z| < π/2`). -/
@[dlmf 28.26.E3]
def goldsteinPhase (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  2 * h * Complex.sinh z - ((m : ℂ) + 1 / 2) * Complex.arctan (Complex.sinh z)

/-- Goldstein's `Fc_m(z, h)`, defined with `Gc_m` so that 28.26.1 holds:
`Fc_m = (π h cosh z)^{1/2} (cos φ Mc^{(1)}_m + sin φ Mc^{(2)}_m)`. -/
@[dlmf 28.26.E1]
def goldsteinFc (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  (π * h * Complex.cosh z) ^ (1 / 2 : ℂ) *
    (Complex.cos (goldsteinPhase m z h) * radialMathieuMc 1 m z h +
      Complex.sin (goldsteinPhase m z h) * radialMathieuMc 2 m z h)

/-- Goldstein's `Gc_m(z, h) = (π h cosh z)^{1/2} (sin φ Mc^{(1)}_m - cos φ Mc^{(2)}_m)`; with
`Fc_m` it gives `Mc^{(3)}_m = e^{iφ} (π h cosh z)^{-1/2} (Fc_m - i Gc_m)` (DLMF 28.26.1). -/
@[dlmf 28.26.E1]
def goldsteinGc (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  (π * h * Complex.cosh z) ^ (1 / 2 : ℂ) *
    (Complex.sin (goldsteinPhase m z h) * radialMathieuMc 1 m z h -
      Complex.cos (goldsteinPhase m z h) * radialMathieuMc 2 m z h)

/-- Goldstein's `Fs_m(z, h) = (π h cosh z)^{1/2} (sin φ Ms^{(1)}_{m+1} - cos φ Ms^{(2)}_{m+1})`;
with `Gs_m` it gives `i Ms^{(3)}_{m+1} = e^{iφ} (π h cosh z)^{-1/2} (Fs_m - i Gs_m)`
(DLMF 28.26.2). -/
@[dlmf 28.26.E2]
def goldsteinFs (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  (π * h * Complex.cosh z) ^ (1 / 2 : ℂ) *
    (Complex.sin (goldsteinPhase m z h) * radialMathieuMs 1 (m + 1) z h -
      Complex.cos (goldsteinPhase m z h) * radialMathieuMs 2 (m + 1) z h)

/-- Goldstein's `Gs_m(z, h) = -(π h cosh z)^{1/2} (cos φ Ms^{(1)}_{m+1} + sin φ Ms^{(2)}_{m+1})`
(DLMF 28.26.2). -/
@[dlmf 28.26.E2]
def goldsteinGs (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  -((π * h * Complex.cosh z) ^ (1 / 2 : ℂ) *
    (Complex.cos (goldsteinPhase m z h) * radialMathieuMs 1 (m + 1) z h +
      Complex.sin (goldsteinPhase m z h) * radialMathieuMs 2 (m + 1) z h))

/-- The partial sum `1 + s/(8h cosh² z) + … ` of Goldstein's expansion 28.26.4 of `Fc_m`
through the `h⁻³` term, `s = 2m + 1`. -/
def goldsteinFcApprox (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  let s : ℂ := 2 * m + 1
  let C := Complex.cosh z
  1 + s / (8 * h * C ^ 2) +
    1 / (2 ^ 11 * h ^ 2) *
      ((s ^ 4 + 86 * s ^ 2 + 105) / C ^ 4 - (s ^ 4 + 22 * s ^ 2 + 57) / C ^ 2) +
    1 / (2 ^ 14 * h ^ 3) * (-(s ^ 5 + 14 * s ^ 3 + 33 * s) / C ^ 2 -
      (2 * s ^ 5 + 124 * s ^ 3 + 1122 * s) / C ^ 4 + (3 * s ^ 5 + 290 * s ^ 3 + 1627 * s) / C ^ 6)

/-- The partial sum of Goldstein's expansion 28.26.5 of `Gc_m` through the `h⁻³` term. -/
def goldsteinGcApprox (m : ℕ) (z : ℂ) (h : ℝ) : ℂ :=
  let s : ℂ := 2 * m + 1
  let C := Complex.cosh z
  Complex.sinh z / C ^ 2 * ((s ^ 2 + 3) / (2 ^ 5 * h) +
    1 / (2 ^ 9 * h ^ 2) * (s ^ 3 + 3 * s + (4 * s ^ 3 + 44 * s) / C ^ 2) +
    1 / (2 ^ 14 * h ^ 3) * (5 * s ^ 4 + 34 * s ^ 2 + 9 -
      (s ^ 6 - 47 * s ^ 4 + 667 * s ^ 2 + 2835) / (12 * C ^ 2) +
      (s ^ 6 + 505 * s ^ 4 + 12139 * s ^ 2 + 10395) / (12 * C ^ 4)))

/-! ### Kernels and paths of §28.28 -/

/-- `w = cosh z cos t cos α + sinh z sin t sin α` (DLMF 28.28.1). -/
@[dlmf 28.28.E1]
def mathieuKernelW (z t α : ℂ) : ℂ :=
  Complex.cosh z * Complex.cos t * Complex.cos α + Complex.sinh z * Complex.sin t * Complex.sin α

/-- The integral along the path `𝓛_j` of DLMF 28.28.6, realized as a polygonal path with
vertical rays: `𝓛_1` from `-η₁ + i∞` down to `-η₁`, along `[-η₁, 2π - η₁]` and up to
`2π - η₁ + i∞`; `𝓛_3` from `-η₁ + i∞` down to `-η₁`, along `[-η₁, η₂]` and down to
`η₂ - i∞`; `𝓛_4` from `η₂ - i∞` up to `η₂`, along `[η₂, 2π - η₁]` and up to
`2π - η₁ + i∞`. Junk `0` for other `j`. -/
@[dlmf 28.28.E6]
def mathieuPathIntegral (j : ℕ) (η₁ η₂ : ℝ) (f : ℂ → ℂ) : ℂ :=
  match j with
  | 1 => -I * (∫ s in Ioi (0 : ℝ), f (-η₁ + I * s)) +
      (∫ x in (-η₁)..(2 * π - η₁), f x) + I * ∫ s in Ioi (0 : ℝ), f (2 * π - η₁ + I * s)
  | 3 => -I * (∫ s in Ioi (0 : ℝ), f (-η₁ + I * s)) +
      (∫ x in (-η₁)..η₂, f x) - I * ∫ s in Ioi (0 : ℝ), f (η₂ - I * s)
  | 4 => I * (∫ s in Ioi (0 : ℝ), f (η₂ - I * s)) +
      (∫ x in η₂..(2 * π - η₁), f x) + I * ∫ s in Ioi (0 : ℝ), f (2 * π - η₁ + I * s)
  | _ => 0

/-- `log (2R(z, t) e^{-z}) = ½ (log(1 + e^{-2(z - it)}) + log(1 + e^{-2(z + it)}))`, analytic
for `Re z > 0` (principal logarithms of numbers with positive real part). -/
def mathieuKernelLogR (z t : ℂ) : ℂ :=
  (Complex.log (1 + Complex.exp (-2 * (z - I * t))) +
    Complex.log (1 + Complex.exp (-2 * (z + I * t)))) / 2

/-- `R(z, t)` of DLMF 28.28.18: the analytic function on `Re z > 0` (real `t`) with
`R² = ½(cosh 2z + cos 2t)` and `R(z, 0) = cosh z`, written as `R = e^{z + log(2R e^{-z})} / 2`. -/
@[dlmf 28.28.E18]
def mathieuKernelR (z t : ℂ) : ℂ :=
  Complex.exp (z + mathieuKernelLogR z t) / 2

/-- `φ(z, t)` of DLMF 28.28.19: the analytic function on `Re z > 0` (real `t`) with
`e^{2iφ} = cosh(z + it) / cosh(z - it)` and `φ(z, 0) = 0`:
`φ = t + (log(1 + e^{-2(z+it)}) - log(1 + e^{-2(z-it)})) / (2i)`. -/
@[dlmf 28.28.E19]
def mathieuKernelPhi (z t : ℂ) : ℂ :=
  t + (Complex.log (1 + Complex.exp (-2 * (z + I * t))) -
    Complex.log (1 + Complex.exp (-2 * (z - I * t)))) / (2 * I)

/-- `𝒞^{(j)}_μ(2hR(z, t))` continued analytically from real `z > 0` through `Re z > 0`
(DLMF 28.28.17): `𝒞^{(j)}_μ(h e^{z'})` with `z' = z + log(2R e^{-z})`. -/
def mathieuCylR (j : ℕ) (μ h z t : ℂ) : ℂ :=
  mathieuCylExp j μ h (z + mathieuKernelLogR z t)

/-! ### Cross-products and integrals of §28.28(iii)–(iv) -/

/-- `D_0(ν, μ, z) = M^{(3)}_ν(z) M^{(4)}_μ(z) - M^{(4)}_ν(z) M^{(3)}_μ(z)` (DLMF 28.28.24). -/
@[dlmf 28.28.E24]
def modMathieuD0 (ν μ z h : ℂ) : ℂ :=
  modMathieuM 3 ν z h * modMathieuM 4 μ z h - modMathieuM 4 ν z h * modMathieuM 3 μ z h

/-- `D_1(ν, μ, z) = M^{(3)'}_ν(z) M^{(4)}_μ(z) - M^{(4)'}_ν(z) M^{(3)}_μ(z)` (DLMF 28.28.24). -/
@[dlmf 28.28.E24]
def modMathieuD1 (ν μ z h : ℂ) : ℂ :=
  deriv (fun z => modMathieuM 3 ν z h) z * modMathieuM 4 μ z h -
    deriv (fun z => modMathieuM 4 ν z h) z * modMathieuM 3 μ z h

/-- `α^{(0)}_{ν,m} = (2π)⁻¹ ∫₀^{2π} cos t me_ν(t, h²) me_{-ν-2m-1}(t, h²) dt`
(DLMF 28.28.27, first equality). -/
@[dlmf 28.28.E27]
def mathieuAlpha0 (ν : ℂ) (m : ℤ) (h : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    Complex.cos t * mathieuMe ν t (h ^ 2) * mathieuMe (-ν - 2 * m - 1) t (h ^ 2)

/-- `α^{(1)}_{ν,m} = (2π)⁻¹ ∫₀^{2π} sin t me_ν(t, h²) me_{-ν-2m-1}(t, h²) dt`
(DLMF 28.28.28, first equality). -/
@[dlmf 28.28.E28]
def mathieuAlpha1 (ν : ℂ) (m : ℤ) (h : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    Complex.sin t * mathieuMe ν t (h ^ 2) * mathieuMe (-ν - 2 * m - 1) t (h ^ 2)

/-- `γ_{ν,m} = (2π)⁻¹ ∫₀^{2π} me'_ν(t, h²) me_{-ν-2m}(t, h²) dt` (DLMF 28.28.33, first
equality). -/
@[dlmf 28.28.E33]
def mathieuGammaInt (ν : ℂ) (m : ℤ) (h : ℂ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    deriv (fun x => mathieuMe ν x (h ^ 2)) t * mathieuMe (-ν - 2 * m) t (h ^ 2)

/-- `Ds_0(n, m, z) = Ms^{(3)}_n Ms^{(4)}_m - Ms^{(4)}_n Ms^{(3)}_m` (DLMF 28.28.35). -/
@[dlmf 28.28.E35]
def radialMathieuDs0 (n m : ℕ) (z h : ℂ) : ℂ :=
  radialMathieuMs 3 n z h * radialMathieuMs 4 m z h -
    radialMathieuMs 4 n z h * radialMathieuMs 3 m z h

/-- `Ds_1(n, m, z) = Ms^{(3)'}_n Ms^{(4)}_m - Ms^{(4)'}_n Ms^{(3)}_m` (DLMF 28.28.35). -/
@[dlmf 28.28.E35]
def radialMathieuDs1 (n m : ℕ) (z h : ℂ) : ℂ :=
  deriv (fun z => radialMathieuMs 3 n z h) z * radialMathieuMs 4 m z h -
    deriv (fun z => radialMathieuMs 4 n z h) z * radialMathieuMs 3 m z h

/-- `Ds_2(n, m, z) = Ms^{(3)'}_n Ms^{(4)'}_m - Ms^{(4)'}_n Ms^{(3)'}_m` (DLMF 28.28.35). -/
@[dlmf 28.28.E35]
def radialMathieuDs2 (n m : ℕ) (z h : ℂ) : ℂ :=
  deriv (fun z => radialMathieuMs 3 n z h) z * deriv (fun z => radialMathieuMs 4 m z h) z -
    deriv (fun z => radialMathieuMs 4 n z h) z * deriv (fun z => radialMathieuMs 3 m z h) z

/-- `Dc_0(n, m, z) = Mc^{(3)}_n Mc^{(4)}_m - Mc^{(4)}_n Mc^{(3)}_m` (DLMF 28.28.39). -/
@[dlmf 28.28.E39]
def radialMathieuDc0 (n m : ℕ) (z h : ℂ) : ℂ :=
  radialMathieuMc 3 n z h * radialMathieuMc 4 m z h -
    radialMathieuMc 4 n z h * radialMathieuMc 3 m z h

/-- `Dc_1(n, m, z) = Mc^{(3)'}_n Mc^{(4)}_m - Mc^{(4)'}_n Mc^{(3)}_m` (DLMF 28.28.39). -/
@[dlmf 28.28.E39]
def radialMathieuDc1 (n m : ℕ) (z h : ℂ) : ℂ :=
  deriv (fun z => radialMathieuMc 3 n z h) z * radialMathieuMc 4 m z h -
    deriv (fun z => radialMathieuMc 4 n z h) z * radialMathieuMc 3 m z h

/-- `Dsc_0(n, m, z) = Ms^{(3)}_n Mc^{(4)}_m - Ms^{(4)}_n Mc^{(3)}_m` (DLMF 28.28.40). -/
@[dlmf 28.28.E40]
def radialMathieuDsc0 (n m : ℕ) (z h : ℂ) : ℂ :=
  radialMathieuMs 3 n z h * radialMathieuMc 4 m z h -
    radialMathieuMs 4 n z h * radialMathieuMc 3 m z h

/-- `Dsc_1(n, m, z) = Ms^{(3)'}_n Mc^{(4)}_m - Ms^{(4)'}_n Mc^{(3)}_m` (DLMF 28.28.40). -/
@[dlmf 28.28.E40]
def radialMathieuDsc1 (n m : ℕ) (z h : ℂ) : ℂ :=
  deriv (fun z => radialMathieuMs 3 n z h) z * radialMathieuMc 4 m z h -
    deriv (fun z => radialMathieuMs 4 n z h) z * radialMathieuMc 3 m z h

/-- `α̂^{(s)}_{n,m} = (2π)⁻¹ ∫₀^{2π} cos t se_n(t, h²) se_m(t, h²) dt` (DLMF 28.28.38, first
equality), real `h`. -/
@[dlmf 28.28.E38]
def mathieuAlphaHatS (n m : ℕ) (h : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    Complex.cos t * mathieuSe n t (h ^ 2) * mathieuSe m t (h ^ 2)

/-- `β̂_{n,m} = (2π)⁻¹ ∫₀^{2π} sin t se_n(t, h²) ce_m(t, h²) dt` (DLMF 28.28.43, first
equality), real `h`. -/
@[dlmf 28.28.E43]
def mathieuBetaHat (n m : ℕ) (h : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    Complex.sin t * mathieuSe n t (h ^ 2) * mathieuCe m t (h ^ 2)

/-- `γ̂_{n,m} = (2π)⁻¹ ∫₀^{2π} se'_n(t, h²) ce_m(t, h²) dt` (DLMF 28.28.46, first equality),
real `h`. -/
@[dlmf 28.28.E46]
def mathieuGammaHat (n m : ℕ) (h : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    deriv (fun x => mathieuSe n x (h ^ 2)) t * mathieuCe m t (h ^ 2)

/-- `α̂^{(c)}_{n,m} = (2π)⁻¹ ∫₀^{2π} cos t ce_n(t, h²) ce_m(t, h²) dt` (DLMF 28.28.49, first
equality), real `h`. -/
@[dlmf 28.28.E49]
def mathieuAlphaHatC (n m : ℕ) (h : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * π,
    Complex.cos t * mathieuCe n t (h ^ 2) * mathieuCe m t (h ^ 2)

/-- The **valley conditions** for the paths `𝓛_j` (DLMF 28.28.6, made explicit): with
`C₊ = cosh(z + iα)`, `C₋ = cosh(z - iα)` the integrand `e^{2ihw} me_ν(t)` decays
double-exponentially on the upper rays `Re t = -η₁` (and `2π - η₁`) when
`arg(C₊ + i) - π < -η₁ < arg(C₊ - i)`, and on the lower ray `Re t = η₂` when
`-arg(C₋ - i) < η₂ < π - arg(C₋ + i)` (`h > 0`; principal arguments). DLMF only says
"`η₁`, `η₂` real constants"; the formulas fail for other choices (the rays must lie in
these valleys, and shifting `η₂` by `2π` changes the value). -/
def MathieuPathValley (z α : ℂ) (η₁ η₂ : ℝ) : Prop :=
  (Complex.arg (Complex.cosh (z + I * α) + I) - π < -η₁ ∧
      -η₁ < Complex.arg (Complex.cosh (z + I * α) - I)) ∧
    (-Complex.arg (Complex.cosh (z - I * α) - I) < η₂ ∧
      η₂ < π - Complex.arg (Complex.cosh (z - I * α) + I))

/-- The common denominator `sinh² z + sin² t` of §28.28(iii)–(iv). -/
abbrev m28c_den (z : ℂ) (t : ℝ) : ℂ := Complex.sinh z ^ 2 + Complex.sin t ^ 2

end DLMF.Mathieu
