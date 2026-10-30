/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Noninteger.Basic
public import DLMF.Bessel.Basic

/-!
# Modified Mathieu functions, cylinder expansions and joining factors
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

end DLMF.Mathieu
