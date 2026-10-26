/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Fourier series of the Mathieu functions (DLMF §28.4)

The Fourier coefficients `A^n_m(q) = mathieuFourierA n m q`, `B^n_m(q) = mathieuFourierB n m q`
of `ce_n`, `se_n` (real `q`) are defined in `DLMF.Mathieu.Basic` as the Fourier integrals, so
that the expansions 28.4.1–28.4.4 are statements of convergence (admitted here, together with
the recurrences 28.4.5–28.4.8, the normalizations 28.4.9–28.4.12, the values at `q = 0`, the
change of sign of `q` and the asymptotic forms 28.4.21–28.4.27).

Small-`q` forms such as 28.4.21, `A_{2s} = (c q^s + O(q^{s+2})) A_0`, are stated with an
explicit error function `ε` with `ε = O(q^{s+2})` as `q → 0`; the large-`m` forms 28.4.24–28.4.27
likewise with `ε = O(1/m)` as `m → ∞` (`q ≠ 0` fixed). This avoids dividing by `A_0`.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-! ### Fourier expansions (§28.4(i)) -/

/-- **DLMF 28.4.1**: `ce_{2n}(z, q) = ∑_{m ≥ 0} A^{2n}_{2m}(q) cos 2mz`, real `q`, `z ∈ ℂ`. -/
@[dlmf 28.4.E1]
theorem hasSum_mathieuCe_even (n : ℕ) (q : ℝ) (z : ℂ) :
    HasSum (fun m : ℕ => mathieuFourierA (2 * n) (2 * m) q * Complex.cos (2 * m * z))
      (mathieuCe (2 * n) z q) := by
  sorry

/-- **DLMF 28.4.2**: `ce_{2n+1}(z, q) = ∑_{m ≥ 0} A^{2n+1}_{2m+1}(q) cos(2m+1)z`. -/
@[dlmf 28.4.E2]
theorem hasSum_mathieuCe_odd (n : ℕ) (q : ℝ) (z : ℂ) :
    HasSum (fun m : ℕ => mathieuFourierA (2 * n + 1) (2 * m + 1) q *
      Complex.cos ((2 * m + 1) * z)) (mathieuCe (2 * n + 1) z q) := by
  sorry

/-- **DLMF 28.4.3**: `se_{2n+1}(z, q) = ∑_{m ≥ 0} B^{2n+1}_{2m+1}(q) sin(2m+1)z`. -/
@[dlmf 28.4.E3]
theorem hasSum_mathieuSe_odd (n : ℕ) (q : ℝ) (z : ℂ) :
    HasSum (fun m : ℕ => mathieuFourierB (2 * n + 1) (2 * m + 1) q *
      Complex.sin ((2 * m + 1) * z)) (mathieuSe (2 * n + 1) z q) := by
  sorry

/-- **DLMF 28.4.4**: `se_{2n+2}(z, q) = ∑_{m ≥ 0} B^{2n+2}_{2m+2}(q) sin(2m+2)z`. -/
@[dlmf 28.4.E4]
theorem hasSum_mathieuSe_even (n : ℕ) (q : ℝ) (z : ℂ) :
    HasSum (fun m : ℕ => mathieuFourierB (2 * n + 2) (2 * m + 2) q *
      Complex.sin ((2 * m + 2) * z)) (mathieuSe (2 * n + 2) z q) := by
  sorry

/-- **Absolute and locally uniform convergence** (DLMF §28.4(i)): the Fourier series
`∑ₘ A^n_m(q) cos mz` and `∑ₘ B^n_m(q) sin mz` converge absolutely and uniformly on compact
subsets of `ℂ`. -/
@[dlmf 28.4.i]
theorem mathieu_fourier_locallyUniform (n : ℕ) (q : ℝ) :
    (∀ z : ℂ, Summable fun m : ℕ => ‖mathieuFourierA n m q * Complex.cos (m * z)‖) ∧
      (∀ z : ℂ, Summable fun m : ℕ => ‖mathieuFourierB n m q * Complex.sin (m * z)‖) ∧
      TendstoLocallyUniformly (fun N z => ∑ m ∈ Finset.range N,
        mathieuFourierA n m q * Complex.cos (m * z)) (fun z => mathieuCe n z q) atTop ∧
      (n ≠ 0 → TendstoLocallyUniformly (fun N z => ∑ m ∈ Finset.range N,
        mathieuFourierB n m q * Complex.sin (m * z)) (fun z => mathieuSe n z q) atTop) := by
  sorry

/-! ### Recurrence relations (§28.4(ii)) -/

/-- **DLMF 28.4.5** (first line): `a A_0 - q A_2 = 0`, `a = a_{2n}(q)`,
`A_{2m} = A^{2n}_{2m}(q)`. -/
@[dlmf 28.4.E5]
theorem mathieuFourierA_even_rec_zero (n : ℕ) (q : ℝ) :
    (mathieuA (2 * n) q : ℂ) * mathieuFourierA (2 * n) 0 q -
      q * mathieuFourierA (2 * n) 2 q = 0 := by
  sorry

/-- **DLMF 28.4.5** (second line): `(a - 4) A_2 - q(2A_0 + A_4) = 0`, `a = a_{2n}(q)`. -/
@[dlmf 28.4.E5]
theorem mathieuFourierA_even_rec_one (n : ℕ) (q : ℝ) :
    ((mathieuA (2 * n) q : ℂ) - 4) * mathieuFourierA (2 * n) 2 q -
      q * (2 * mathieuFourierA (2 * n) 0 q + mathieuFourierA (2 * n) 4 q) = 0 := by
  sorry

/-- **DLMF 28.4.5** (general line): `(a - 4m²) A_{2m} - q(A_{2m-2} + A_{2m+2}) = 0`, `m ≥ 2`. -/
@[dlmf 28.4.E5]
theorem mathieuFourierA_even_rec (n : ℕ) (q : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    ((mathieuA (2 * n) q : ℂ) - 4 * m ^ 2) * mathieuFourierA (2 * n) (2 * m) q -
      q * (mathieuFourierA (2 * n) (2 * m - 2) q + mathieuFourierA (2 * n) (2 * m + 2) q) =
      0 := by
  sorry

/-- **DLMF 28.4.6** (first line): `(a - 1 - q) A_1 - q A_3 = 0`, `a = a_{2n+1}(q)`. -/
@[dlmf 28.4.E6]
theorem mathieuFourierA_odd_rec_zero (n : ℕ) (q : ℝ) :
    ((mathieuA (2 * n + 1) q : ℂ) - 1 - q) * mathieuFourierA (2 * n + 1) 1 q -
      q * mathieuFourierA (2 * n + 1) 3 q = 0 := by
  sorry

/-- **DLMF 28.4.6** (general line):
`(a - (2m+1)²) A_{2m+1} - q(A_{2m-1} + A_{2m+3}) = 0`, `m ≥ 1`, `a = a_{2n+1}(q)`. -/
@[dlmf 28.4.E6]
theorem mathieuFourierA_odd_rec (n : ℕ) (q : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ((mathieuA (2 * n + 1) q : ℂ) - (2 * m + 1) ^ 2) * mathieuFourierA (2 * n + 1) (2 * m + 1) q -
      q * (mathieuFourierA (2 * n + 1) (2 * m - 1) q +
        mathieuFourierA (2 * n + 1) (2 * m + 3) q) = 0 := by
  sorry

/-- **DLMF 28.4.7** (first line): `(a - 1 + q) B_1 - q B_3 = 0`, `a = b_{2n+1}(q)`. -/
@[dlmf 28.4.E7]
theorem mathieuFourierB_odd_rec_zero (n : ℕ) (q : ℝ) :
    ((mathieuB (2 * n + 1) q : ℂ) - 1 + q) * mathieuFourierB (2 * n + 1) 1 q -
      q * mathieuFourierB (2 * n + 1) 3 q = 0 := by
  sorry

/-- **DLMF 28.4.7** (general line):
`(a - (2m+1)²) B_{2m+1} - q(B_{2m-1} + B_{2m+3}) = 0`, `m ≥ 1`, `a = b_{2n+1}(q)`. -/
@[dlmf 28.4.E7]
theorem mathieuFourierB_odd_rec (n : ℕ) (q : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ((mathieuB (2 * n + 1) q : ℂ) - (2 * m + 1) ^ 2) * mathieuFourierB (2 * n + 1) (2 * m + 1) q -
      q * (mathieuFourierB (2 * n + 1) (2 * m - 1) q +
        mathieuFourierB (2 * n + 1) (2 * m + 3) q) = 0 := by
  sorry

/-- **DLMF 28.4.8** (first line): `(a - 4) B_2 - q B_4 = 0`, `a = b_{2n+2}(q)`. -/
@[dlmf 28.4.E8]
theorem mathieuFourierB_even_rec_zero (n : ℕ) (q : ℝ) :
    ((mathieuB (2 * n + 2) q : ℂ) - 4) * mathieuFourierB (2 * n + 2) 2 q -
      q * mathieuFourierB (2 * n + 2) 4 q = 0 := by
  sorry

/-- **DLMF 28.4.8** (general line): `(a - 4m²) B_{2m} - q(B_{2m-2} + B_{2m+2}) = 0`, `m ≥ 2`,
`a = b_{2n+2}(q)`. (DLMF's last label `B_{2m+2} = B^{2n+2}_{2m+2}(q)` means
`B_{2m} = B^{2n+2}_{2m}(q)`.) -/
@[dlmf 28.4.E8]
theorem mathieuFourierB_even_rec (n : ℕ) (q : ℝ) {m : ℕ} (hm : 2 ≤ m) :
    ((mathieuB (2 * n + 2) q : ℂ) - 4 * m ^ 2) * mathieuFourierB (2 * n + 2) (2 * m) q -
      q * (mathieuFourierB (2 * n + 2) (2 * m - 2) q +
        mathieuFourierB (2 * n + 2) (2 * m + 2) q) = 0 := by
  sorry

/-! ### Normalization (§28.4(iii)) -/

/-- **DLMF 28.4.9**: `2 (A^{2n}_0)² + ∑_{m ≥ 1} (A^{2n}_{2m})² = 1`. -/
@[dlmf 28.4.E9]
theorem hasSum_mathieuFourierA_even_sq (n : ℕ) (q : ℝ) :
    HasSum (fun m : ℕ => (if m = 0 then 2 else 1) * mathieuFourierA (2 * n) (2 * m) q ^ 2) 1 := by
  sorry

/-- **DLMF 28.4.10**: `∑_{m ≥ 0} (A^{2n+1}_{2m+1})² = 1`. -/
@[dlmf 28.4.E10]
theorem hasSum_mathieuFourierA_odd_sq (n : ℕ) (q : ℝ) :
    HasSum (fun m : ℕ => mathieuFourierA (2 * n + 1) (2 * m + 1) q ^ 2) 1 := by
  sorry

/-- **DLMF 28.4.11**: `∑_{m ≥ 0} (B^{2n+1}_{2m+1})² = 1`. -/
@[dlmf 28.4.E11]
theorem hasSum_mathieuFourierB_odd_sq (n : ℕ) (q : ℝ) :
    HasSum (fun m : ℕ => mathieuFourierB (2 * n + 1) (2 * m + 1) q ^ 2) 1 := by
  sorry

/-- **DLMF 28.4.12**: `∑_{m ≥ 0} (B^{2n+2}_{2m+2})² = 1`. -/
@[dlmf 28.4.E12]
theorem hasSum_mathieuFourierB_even_sq (n : ℕ) (q : ℝ) :
    HasSum (fun m : ℕ => mathieuFourierB (2 * n + 2) (2 * m + 2) q ^ 2) 1 := by
  sorry

/-- **Sign convention** (DLMF §28.4(iii)): the sign ambiguity left by 28.4.9–28.4.12 is resolved
by 28.4.13–28.4.16 at `q = 0` and by continuity in `q`; for real `q` this is equivalent to the
convention `ce_n(0, q) = ∑ₘ A^n_m(q) > 0` and `se_n'(0, q) = ∑ₘ m B^n_m(q) > 0` of
`mathieuCe`, `mathieuSe`. -/
@[dlmf 28.4.iii]
theorem mathieuFourier_sign (n : ℕ) (q : ℝ) :
    HasSum (fun m : ℕ => mathieuFourierA n m q) (mathieuCe n 0 q) ∧
      (n ≠ 0 → HasSum (fun m : ℕ => (m : ℂ) * mathieuFourierB n m q)
        (deriv (fun z => mathieuSe n z q) 0)) ∧
      0 < (mathieuCe n 0 q).re ∧ (mathieuCe n 0 q).im = 0 := by
  sorry

/-! ### The case `q = 0` (§28.4(iv)) -/

/-- **DLMF 28.4.13**: `A^0_0(0) = 1/√2`, `A^{2n}_{2n}(0) = 1` (`n > 0`), `A^{2n}_{2m}(0) = 0`
(`n ≠ m`). -/
@[dlmf 28.4.E13]
theorem mathieuFourierA_even_q_zero (n m : ℕ) :
    mathieuFourierA (2 * n) (2 * m) 0 =
      if n = m then (if n = 0 then 1 / Real.sqrt 2 else 1) else 0 := by
  sorry

/-- **DLMF 28.4.14**: `A^{2n+1}_{2n+1}(0) = 1`, `A^{2n+1}_{2m+1}(0) = 0` (`n ≠ m`). -/
@[dlmf 28.4.E14]
theorem mathieuFourierA_odd_q_zero (n m : ℕ) :
    mathieuFourierA (2 * n + 1) (2 * m + 1) 0 = if n = m then 1 else 0 := by
  sorry

/-- **DLMF 28.4.15**: `B^{2n+1}_{2n+1}(0) = 1`, `B^{2n+1}_{2m+1}(0) = 0` (`n ≠ m`). -/
@[dlmf 28.4.E15]
theorem mathieuFourierB_odd_q_zero (n m : ℕ) :
    mathieuFourierB (2 * n + 1) (2 * m + 1) 0 = if n = m then 1 else 0 := by
  sorry

/-- **DLMF 28.4.16**: `B^{2n+2}_{2n+2}(0) = 1`, `B^{2n+2}_{2m+2}(0) = 0` (`n ≠ m`). -/
@[dlmf 28.4.E16]
theorem mathieuFourierB_even_q_zero (n m : ℕ) :
    mathieuFourierB (2 * n + 2) (2 * m + 2) 0 = if n = m then 1 else 0 := by
  sorry

/-! ### Change of sign of `q` (§28.4(v)) -/

/-- **DLMF 28.4.17**: `A^{2n}_{2m}(-q) = (-1)^{n-m} A^{2n}_{2m}(q)`. -/
@[dlmf 28.4.E17]
theorem mathieuFourierA_even_neg_q (n m : ℕ) (q : ℝ) :
    mathieuFourierA (2 * n) (2 * m) (-q) =
      (-1) ^ ((n : ℤ) - m) * mathieuFourierA (2 * n) (2 * m) q := by
  sorry

/-- **DLMF 28.4.18**: `B^{2n+2}_{2m+2}(-q) = (-1)^{n-m} B^{2n+2}_{2m+2}(q)`. -/
@[dlmf 28.4.E18]
theorem mathieuFourierB_even_neg_q (n m : ℕ) (q : ℝ) :
    mathieuFourierB (2 * n + 2) (2 * m + 2) (-q) =
      (-1) ^ ((n : ℤ) - m) * mathieuFourierB (2 * n + 2) (2 * m + 2) q := by
  sorry

/-- **DLMF 28.4.19**: `A^{2n+1}_{2m+1}(-q) = (-1)^{n-m} B^{2n+1}_{2m+1}(q)`. -/
@[dlmf 28.4.E19]
theorem mathieuFourierA_odd_neg_q (n m : ℕ) (q : ℝ) :
    mathieuFourierA (2 * n + 1) (2 * m + 1) (-q) =
      (-1) ^ ((n : ℤ) - m) * mathieuFourierB (2 * n + 1) (2 * m + 1) q := by
  sorry

/-- **DLMF 28.4.20**: `B^{2n+1}_{2m+1}(-q) = (-1)^{n-m} A^{2n+1}_{2m+1}(q)`. -/
@[dlmf 28.4.E20]
theorem mathieuFourierB_odd_neg_q (n m : ℕ) (q : ℝ) :
    mathieuFourierB (2 * n + 1) (2 * m + 1) (-q) =
      (-1) ^ ((n : ℤ) - m) * mathieuFourierA (2 * n + 1) (2 * m + 1) q := by
  sorry

/-! ### Behavior for small `q` (§28.4(vi)) -/

/-- **DLMF 28.4.21**: for fixed `s ≥ 1`,
`A^0_{2s}(q) = ((-1)^s 2/(s!)² (q/4)^s + O(q^{s+2})) A^0_0(q)` as `q → 0`. -/
@[dlmf 28.4.E21]
theorem mathieuFourierA_zero_small_q {s : ℕ} (hs : 1 ≤ s) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 2)) ∧ ∀ q : ℝ,
      mathieuFourierA 0 (2 * s) q = ((-1) ^ s * 2 / (s.factorial : ℂ) ^ 2 * ((q : ℂ) / 4) ^ s +
        ε q) * mathieuFourierA 0 0 q := by
  sorry

/-- **DLMF 28.4.22** (`A`): for fixed `s, m ≥ 1`,
`A^m_{m+2s}(q) = ((-1)^s m!/(s!(m+s)!) (q/4)^s + O(q^{s+1})) A^m_m(q)` as `q → 0`. -/
@[dlmf 28.4.E22]
theorem mathieuFourierA_up_small_q {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ q : ℝ,
      mathieuFourierA m (m + 2 * s) q = ((-1) ^ s * (m.factorial : ℂ) /
        ((s.factorial : ℂ) * ((m + s).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierA m m q := by
  sorry

/-- **DLMF 28.4.22** (`B`):
`B^m_{m+2s}(q) = ((-1)^s m!/(s!(m+s)!) (q/4)^s + O(q^{s+1})) B^m_m(q)`. -/
@[dlmf 28.4.E22]
theorem mathieuFourierB_up_small_q {m s : ℕ} (hm : 1 ≤ m) (hs : 1 ≤ s) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ q : ℝ,
      mathieuFourierB m (m + 2 * s) q = ((-1) ^ s * (m.factorial : ℂ) /
        ((s.factorial : ℂ) * ((m + s).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierB m m q := by
  sorry

/-- **DLMF 28.4.23** (`A`): for `1 ≤ s` and `2s ≤ m`,
`A^m_{m-2s}(q) = ((m-s-1)!/(s!(m-1)!) (q/4)^s + O(q^{s+1})) A^m_m(q)` as `q → 0`. -/
@[dlmf 28.4.E23]
theorem mathieuFourierA_down_small_q {m s : ℕ} (hs : 1 ≤ s) (hsm : 2 * s ≤ m) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ q : ℝ,
      mathieuFourierA m (m - 2 * s) q = (((m - s - 1).factorial : ℂ) /
        ((s.factorial : ℂ) * ((m - 1).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierA m m q := by
  sorry

/-- **DLMF 28.4.23** (`B`): for `1 ≤ s` and `2s < m`,
`B^m_{m-2s}(q) = ((m-s-1)!/(s!(m-1)!) (q/4)^s + O(q^{s+1})) B^m_m(q)` as `q → 0`. -/
@[dlmf 28.4.E23]
theorem mathieuFourierB_down_small_q {m s : ℕ} (hs : 1 ≤ s) (hsm : 2 * s < m) :
    ∃ ε : ℝ → ℂ, ε =O[𝓝 0] (fun q : ℝ => q ^ (s + 1)) ∧ ∀ q : ℝ,
      mathieuFourierB m (m - 2 * s) q = (((m - s - 1).factorial : ℂ) /
        ((s.factorial : ℂ) * ((m - 1).factorial : ℂ)) * ((q : ℂ) / 4) ^ s + ε q) *
        mathieuFourierB m m q := by
  sorry

/-! ### Asymptotic forms for large `m` (§28.4(vii)) -/

/-- **DLMF 28.4.24**: as `m → ∞`, fixed `q ≠ 0` and `n`,
`A^{2n}_{2m}(q) / A^{2n}_0(q) = (-1)^m/(m!)² (q/4)^m π(1 + O(1/m)) / w_II(π/2; a_{2n}(q), q)`. -/
@[dlmf 28.4.E24]
theorem mathieuFourierA_even_large_m (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    ∃ ε : ℕ → ℂ, ε =O[atTop] (fun m : ℕ => (1 : ℝ) / m) ∧ ∀ m : ℕ,
      mathieuFourierA (2 * n) (2 * m) q = mathieuFourierA (2 * n) 0 q *
        ((-1) ^ m / (m.factorial : ℂ) ^ 2 * ((q : ℂ) / 4) ^ m * (π * (1 + ε m)) /
          mathieuWII (mathieuA (2 * n) q) q (π / 2)) := by
  sorry

/-- **DLMF 28.4.25**: as `m → ∞`, fixed `q ≠ 0` and `n`,
`A^{2n+1}_{2m+1}/A^{2n+1}_1 = (-1)^{m+1}/((1/2)_{m+1})² (q/4)^{m+1} 2(1 + O(1/m)) /
w_II'(π/2; a_{2n+1}(q), q)`. -/
@[dlmf 28.4.E25]
theorem mathieuFourierA_odd_large_m (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    ∃ ε : ℕ → ℂ, ε =O[atTop] (fun m : ℕ => (1 : ℝ) / m) ∧ ∀ m : ℕ,
      mathieuFourierA (2 * n + 1) (2 * m + 1) q = mathieuFourierA (2 * n + 1) 1 q *
        ((-1) ^ (m + 1) / (ascPochhammer ℂ (m + 1)).eval (1 / 2) ^ 2 * ((q : ℂ) / 4) ^ (m + 1) *
          (2 * (1 + ε m)) / deriv (mathieuWII (mathieuA (2 * n + 1) q) q) (π / 2)) := by
  sorry

/-- **DLMF 28.4.26**: as `m → ∞`, fixed `q ≠ 0` and `n`,
`B^{2n+1}_{2m+1}/B^{2n+1}_1 = (-1)^m/((1/2)_{m+1})² (q/4)^{m+1} 2(1 + O(1/m)) /
w_I(π/2; b_{2n+1}(q), q)`. -/
@[dlmf 28.4.E26]
theorem mathieuFourierB_odd_large_m (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    ∃ ε : ℕ → ℂ, ε =O[atTop] (fun m : ℕ => (1 : ℝ) / m) ∧ ∀ m : ℕ,
      mathieuFourierB (2 * n + 1) (2 * m + 1) q = mathieuFourierB (2 * n + 1) 1 q *
        ((-1) ^ m / (ascPochhammer ℂ (m + 1)).eval (1 / 2) ^ 2 * ((q : ℂ) / 4) ^ (m + 1) *
          (2 * (1 + ε m)) / mathieuWI (mathieuB (2 * n + 1) q) q (π / 2)) := by
  sorry

/-- **DLMF 28.4.27**: as `m → ∞`, fixed `q ≠ 0` and `n`,
`B^{2n+2}_{2m}/B^{2n+2}_2 = (-1)^m/(m!)² (q/4)^m qπ(1 + O(1/m)) / w_I'(π/2; b_{2n+2}(q), q)`. -/
@[dlmf 28.4.E27]
theorem mathieuFourierB_even_large_m (n : ℕ) {q : ℝ} (hq : q ≠ 0) :
    ∃ ε : ℕ → ℂ, ε =O[atTop] (fun m : ℕ => (1 : ℝ) / m) ∧ ∀ m : ℕ,
      mathieuFourierB (2 * n + 2) (2 * m) q = mathieuFourierB (2 * n + 2) 2 q *
        ((-1) ^ m / (m.factorial : ℂ) ^ 2 * ((q : ℂ) / 4) ^ m * (q * π * (1 + ε m)) /
          deriv (mathieuWI (mathieuB (2 * n + 2) q) q) (π / 2)) := by
  sorry

end DLMF.Mathieu
