/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic
public import DLMF.Mathieu.ContFracDefs
public import DLMF.JacobiElliptic.Basic
public import DLMF.EllipticIntegrals.Legendre
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Expansions for small `q` (DLMF §28.6)

The power series 28.6.1–28.6.14 of the eigenvalues `a_n(q)`, `b_n(q)` and 28.6.21–28.6.26 of
`ce_n`, `se_n` converge for small `|q|`; DLMF gives their leading terms. They are stated here as
`Asymptotics.IsBigO` statements as `q → 0` (real `q`), with the remainder of the order of the
first omitted power. All coefficients were checked numerically (eigenvalues of the
tridiagonal recurrence matrices of 28.4.5–28.4.8 at 40 digits).

**Check (28.6.12, 28.6.13).** The coefficients of `q⁶` in `a₆(q)` and `b₆(q)` are
`6743617/92935987200000` and `-5861633/92935987200000`, as DLMF prints them (with the digit
grouping `9293 59872 00000`). Numerically
`(a₆(q) - 36 - q²/70 - 187q⁴/43904000)/q⁶ → 7.2562…·10⁻⁸`, and with the corrected values
`a₆ - b₆ = q⁶/7372800 + O(q⁸)`, which is 28.6.15 for `m = 6`, while `(a₆ + b₆)/2` matches
the general formula 28.6.14 at `m = 6`.

**Remark (28.6.16, `n = 0`).** For `n = 0` the left side of 28.6.16 reduces to `a`, and the
relation needs a factor 2: `a₀ = -2q²/(4 - a₀ - q²/(16 - a₀ - ⋯))`; it is stated separately.

The radii of convergence of Table 28.6.1 are numerical (excluded); the conjecture that they grow
like `n²` is not acquired; 28.6.20 is stated in terms of analytic continuation to discs.
-/

@[expose] public noncomputable section

open Complex Set Filter Asymptotics
open scoped Topology Real

namespace DLMF.Mathieu

/-! ### Eigenvalues (§28.6(i)) -/

/-- **DLMF 28.6.1**: `a₀(q) = -q²/2 + 7q⁴/128 - 29q⁶/2304 + 68687q⁸/18874368 + O(q¹⁰)`. -/
@[dlmf 28.6.E1]
theorem mathieuA_zero_small_q :
    (fun q : ℝ => mathieuA 0 q - (-(1 / 2) * q ^ 2 + 7 / 128 * q ^ 4 - 29 / 2304 * q ^ 6 +
      68687 / 18874368 * q ^ 8)) =O[𝓝 0] (fun q => q ^ 10) := by
  sorry

/-- **DLMF 28.6.2**: `a₁(q) = 1 + q - q²/8 - q³/64 - q⁴/1536 + 11q⁵/36864 + 49q⁶/589824
+ 55q⁷/9437184 - 83q⁸/35389440 + O(q⁹)`. -/
@[dlmf 28.6.E2]
theorem mathieuA_one_small_q :
    (fun q : ℝ => mathieuA 1 q - (1 + q - 1 / 8 * q ^ 2 - 1 / 64 * q ^ 3 - 1 / 1536 * q ^ 4 +
      11 / 36864 * q ^ 5 + 49 / 589824 * q ^ 6 + 55 / 9437184 * q ^ 7 -
      83 / 35389440 * q ^ 8)) =O[𝓝 0] (fun q => q ^ 9) := by
  sorry

/-- **DLMF 28.6.3**: `b₁(q) = 1 - q - q²/8 + q³/64 - q⁴/1536 - 11q⁵/36864 + 49q⁶/589824
- 55q⁷/9437184 - 83q⁸/35389440 + O(q⁹)`. -/
@[dlmf 28.6.E3]
theorem mathieuB_one_small_q :
    (fun q : ℝ => mathieuB 1 q - (1 - q - 1 / 8 * q ^ 2 + 1 / 64 * q ^ 3 - 1 / 1536 * q ^ 4 -
      11 / 36864 * q ^ 5 + 49 / 589824 * q ^ 6 - 55 / 9437184 * q ^ 7 -
      83 / 35389440 * q ^ 8)) =O[𝓝 0] (fun q => q ^ 9) := by
  sorry

/-- **DLMF 28.6.4**: `a₂(q) = 4 + 5q²/12 - 763q⁴/13824 + 1002401q⁶/79626240
- 1669068401q⁸/458647142400 + O(q¹⁰)`. -/
@[dlmf 28.6.E4]
theorem mathieuA_two_small_q :
    (fun q : ℝ => mathieuA 2 q - (4 + 5 / 12 * q ^ 2 - 763 / 13824 * q ^ 4 +
      1002401 / 79626240 * q ^ 6 - 1669068401 / 458647142400 * q ^ 8)) =O[𝓝 0]
      (fun q => q ^ 10) := by
  sorry

/-- **DLMF 28.6.5**: `b₂(q) = 4 - q²/12 + 5q⁴/13824 - 289q⁶/79626240
+ 21391q⁸/458647142400 + O(q¹⁰)`. -/
@[dlmf 28.6.E5]
theorem mathieuB_two_small_q :
    (fun q : ℝ => mathieuB 2 q - (4 - 1 / 12 * q ^ 2 + 5 / 13824 * q ^ 4 -
      289 / 79626240 * q ^ 6 + 21391 / 458647142400 * q ^ 8)) =O[𝓝 0]
      (fun q => q ^ 10) := by
  sorry

/-- **DLMF 28.6.6**: `a₃(q) = 9 + q²/16 + q³/64 + 13q⁴/20480 - 5q⁵/16384 - 1961q⁶/23592960
- 609q⁷/104857600 + O(q⁸)`. -/
@[dlmf 28.6.E6]
theorem mathieuA_three_small_q :
    (fun q : ℝ => mathieuA 3 q - (9 + 1 / 16 * q ^ 2 + 1 / 64 * q ^ 3 + 13 / 20480 * q ^ 4 -
      5 / 16384 * q ^ 5 - 1961 / 23592960 * q ^ 6 - 609 / 104857600 * q ^ 7)) =O[𝓝 0]
      (fun q => q ^ 8) := by
  sorry

/-- **DLMF 28.6.7**: `b₃(q) = 9 + q²/16 - q³/64 + 13q⁴/20480 + 5q⁵/16384 - 1961q⁶/23592960
+ 609q⁷/104857600 + O(q⁸)`. -/
@[dlmf 28.6.E7]
theorem mathieuB_three_small_q :
    (fun q : ℝ => mathieuB 3 q - (9 + 1 / 16 * q ^ 2 - 1 / 64 * q ^ 3 + 13 / 20480 * q ^ 4 +
      5 / 16384 * q ^ 5 - 1961 / 23592960 * q ^ 6 + 609 / 104857600 * q ^ 7)) =O[𝓝 0]
      (fun q => q ^ 8) := by
  sorry

/-- **DLMF 28.6.8**: `a₄(q) = 16 + q²/30 + 433q⁴/864000 - 5701q⁶/2721600000 + O(q⁸)`. -/
@[dlmf 28.6.E8]
theorem mathieuA_four_small_q :
    (fun q : ℝ => mathieuA 4 q - (16 + 1 / 30 * q ^ 2 + 433 / 864000 * q ^ 4 -
      5701 / 2721600000 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 8) := by
  sorry

/-- **DLMF 28.6.9**: `b₄(q) = 16 + q²/30 - 317q⁴/864000 + 10049q⁶/2721600000 + O(q⁸)`. -/
@[dlmf 28.6.E9]
theorem mathieuB_four_small_q :
    (fun q : ℝ => mathieuB 4 q - (16 + 1 / 30 * q ^ 2 - 317 / 864000 * q ^ 4 +
      10049 / 2721600000 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 8) := by
  sorry

/-- **DLMF 28.6.10**: `a₅(q) = 25 + q²/48 + 11q⁴/774144 + q⁵/147456 + 37q⁶/891813888
+ O(q⁷)`. -/
@[dlmf 28.6.E10]
theorem mathieuA_five_small_q :
    (fun q : ℝ => mathieuA 5 q - (25 + 1 / 48 * q ^ 2 + 11 / 774144 * q ^ 4 +
      1 / 147456 * q ^ 5 + 37 / 891813888 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 7) := by
  sorry

/-- **DLMF 28.6.11**: `b₅(q) = 25 + q²/48 + 11q⁴/774144 - q⁵/147456 + 37q⁶/891813888
+ O(q⁷)`. -/
@[dlmf 28.6.E11]
theorem mathieuB_five_small_q :
    (fun q : ℝ => mathieuB 5 q - (25 + 1 / 48 * q ^ 2 + 11 / 774144 * q ^ 4 -
      1 / 147456 * q ^ 5 + 37 / 891813888 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 7) := by
  sorry

/-- **DLMF 28.6.12**: `a₆(q) = 36 + q²/70 + 187q⁴/43904000
+ 6743617q⁶/92935987200000 + O(q⁸)`. -/
@[dlmf 28.6.E12]
theorem mathieuA_six_small_q :
    (fun q : ℝ => mathieuA 6 q - (36 + 1 / 70 * q ^ 2 + 187 / 43904000 * q ^ 4 +
      6743617 / 92935987200000 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 8) := by
  sorry

/-- **DLMF 28.6.13**: `b₆(q) = 36 + q²/70 + 187q⁴/43904000
- 5861633q⁶/92935987200000 + O(q⁸)`. -/
@[dlmf 28.6.E13]
theorem mathieuB_six_small_q :
    (fun q : ℝ => mathieuB 6 q - (36 + 1 / 70 * q ^ 2 + 187 / 43904000 * q ^ 4 -
      5861633 / 92935987200000 * q ^ 6)) =O[𝓝 0] (fun q => q ^ 8) := by
  sorry

/-- **DLMF 28.6.14** (`a_m`), `m ≥ 7`: `a_m(q) = m² + q²/(2(m²-1)) + (5m²+7)q⁴/(32(m²-1)³(m²-4))
+ (9m⁴+58m²+29)q⁶/(64(m²-1)⁵(m²-4)(m²-9)) + O(q^{min(m,8)})`. -/
@[dlmf 28.6.E14]
theorem mathieuA_small_q {m : ℕ} (hm : 7 ≤ m) :
    (fun q : ℝ => mathieuA m q - ((m : ℝ) ^ 2 + q ^ 2 / (2 * ((m : ℝ) ^ 2 - 1)) +
      (5 * (m : ℝ) ^ 2 + 7) * q ^ 4 / (32 * ((m : ℝ) ^ 2 - 1) ^ 3 * ((m : ℝ) ^ 2 - 4)) +
      (9 * (m : ℝ) ^ 4 + 58 * (m : ℝ) ^ 2 + 29) * q ^ 6 /
        (64 * ((m : ℝ) ^ 2 - 1) ^ 5 * ((m : ℝ) ^ 2 - 4) * ((m : ℝ) ^ 2 - 9)))) =O[𝓝 0]
      (fun q => q ^ min m 8) := by
  sorry

/-- **DLMF 28.6.14** (`b_m`), `m ≥ 7`: the same expansion for `b_m(q)`. -/
@[dlmf 28.6.E14]
theorem mathieuB_small_q {m : ℕ} (hm : 7 ≤ m) :
    (fun q : ℝ => mathieuB m q - ((m : ℝ) ^ 2 + q ^ 2 / (2 * ((m : ℝ) ^ 2 - 1)) +
      (5 * (m : ℝ) ^ 2 + 7) * q ^ 4 / (32 * ((m : ℝ) ^ 2 - 1) ^ 3 * ((m : ℝ) ^ 2 - 4)) +
      (9 * (m : ℝ) ^ 4 + 58 * (m : ℝ) ^ 2 + 29) * q ^ 6 /
        (64 * ((m : ℝ) ^ 2 - 1) ^ 5 * ((m : ℝ) ^ 2 - 4) * ((m : ℝ) ^ 2 - 9)))) =O[𝓝 0]
      (fun q => q ^ min m 8) := by
  sorry

/-- **DLMF 28.6.15**: `a_m(q) - b_m(q) = 2q^m/(2^{m-1}(m-1)!)² (1 + O(q²))`, `m ≥ 1`.
In particular (§28.6(i)) the power series of `a_m` and `b_m` agree up to the terms in `q^{m-1}`
(for `m = 2n` up to `q^{2n-2}`, for `m = 2n+1` up to `q^{2n}`). -/
@[dlmf 28.6.E15]
theorem mathieuA_sub_mathieuB_small_q {m : ℕ} (hm : 1 ≤ m) :
    ∃ ε : ℝ → ℝ, ε =O[𝓝 0] (fun q => q ^ 2) ∧ ∀ q : ℝ,
      mathieuA m q - mathieuB m q =
        2 * q ^ m / (2 ^ (m - 1) * ((m - 1).factorial : ℝ)) ^ 2 * (1 + ε q) := by
  sorry

/-- **DLMF 28.6.16** (`n ≥ 1`): for `a = a_{2n}(q)`,
`a - (2n)² - q²/(a - (2n-2)² - ⋯ q²/(a - 2² - 2q²/a)) = -q²/((2n+2)² - a - q²/((2n+4)² - a - ⋯))`;
the right side is the limit of the truncations `mathieuCFTail`. The left-side partial
denominators are assumed nonzero. -/
@[dlmf 28.6.E16]
theorem mathieuA_even_contFrac {n : ℕ} (hn : 1 ≤ n) {q : ℝ}
    (hE : ∀ k < n, mathieuCFHead q (mathieuA (2 * n) q) (mathieuA (2 * n) q)
      (fun k => if k = 0 then 2 else 1) (fun k => (2 * k + 2) ^ 2) k ≠ 0) :
    Tendsto (fun N => -mathieuCFTail q (mathieuA (2 * n) q) (fun k => (2 * n + 2 * k + 2) ^ 2) N)
      atTop (𝓝 (mathieuCFHead q (mathieuA (2 * n) q) (mathieuA (2 * n) q)
        (fun k => if k = 0 then 2 else 1) (fun k => (2 * k + 2) ^ 2) n)) := by
  sorry

/-- **DLMF 28.6.16, case `n = 0`**: `a₀(q) = -2q²/(4 - a₀ - q²/(16 - a₀ - ⋯))` (the printed
pattern degenerates at `n = 0`; the factor 2 comes from 28.4.5). -/
@[dlmf 28.6.E16]
theorem mathieuA_zero_contFrac (q : ℝ) :
    Tendsto (fun N => -2 * mathieuCFTail q (mathieuA 0 q) (fun k => (2 * k + 2) ^ 2) N)
      atTop (𝓝 (mathieuA 0 q : ℂ)) := by
  sorry

/-- **DLMF 28.6.17**: for `a = a_{2n+1}(q)`,
`a - (2n+1)² - q²/(a - (2n-1)² - ⋯ q²/(a - 3² - q²/(a - 1² - q)))
= -q²/((2n+3)² - a - q²/((2n+5)² - a - ⋯))`. -/
@[dlmf 28.6.E17]
theorem mathieuA_odd_contFrac (n : ℕ) {q : ℝ}
    (hE : ∀ k < n, mathieuCFHead q (mathieuA (2 * n + 1) q) (mathieuA (2 * n + 1) q - 1 - q)
      (fun _ => 1) (fun k => (2 * k + 3) ^ 2) k ≠ 0) :
    Tendsto (fun N => -mathieuCFTail q (mathieuA (2 * n + 1) q)
        (fun k => (2 * n + 2 * k + 3) ^ 2) N)
      atTop (𝓝 (mathieuCFHead q (mathieuA (2 * n + 1) q) (mathieuA (2 * n + 1) q - 1 - q)
        (fun _ => 1) (fun k => (2 * k + 3) ^ 2) n)) := by
  sorry

/-- **DLMF 28.6.18**: for `a = b_{2n+1}(q)`,
`a - (2n+1)² - q²/(a - (2n-1)² - ⋯ q²/(a - 3² - q²/(a - 1² + q)))
= -q²/((2n+3)² - a - q²/((2n+5)² - a - ⋯))`. -/
@[dlmf 28.6.E18]
theorem mathieuB_odd_contFrac (n : ℕ) {q : ℝ}
    (hE : ∀ k < n, mathieuCFHead q (mathieuB (2 * n + 1) q) (mathieuB (2 * n + 1) q - 1 + q)
      (fun _ => 1) (fun k => (2 * k + 3) ^ 2) k ≠ 0) :
    Tendsto (fun N => -mathieuCFTail q (mathieuB (2 * n + 1) q)
        (fun k => (2 * n + 2 * k + 3) ^ 2) N)
      atTop (𝓝 (mathieuCFHead q (mathieuB (2 * n + 1) q) (mathieuB (2 * n + 1) q - 1 + q)
        (fun _ => 1) (fun k => (2 * k + 3) ^ 2) n)) := by
  sorry

/-- **DLMF 28.6.19**: for `a = b_{2n+2}(q)`,
`a - (2n+2)² - q²/(a - (2n)² - ⋯ q²/(a - 2²)) = -q²/((2n+4)² - a - q²/((2n+6)² - a - ⋯))`. -/
@[dlmf 28.6.E19]
theorem mathieuB_even_contFrac (n : ℕ) {q : ℝ}
    (hE : ∀ k < n, mathieuCFHead q (mathieuB (2 * n + 2) q) (mathieuB (2 * n + 2) q - 4)
      (fun _ => 1) (fun k => (2 * k + 4) ^ 2) k ≠ 0) :
    Tendsto (fun N => -mathieuCFTail q (mathieuB (2 * n + 2) q)
        (fun k => (2 * n + 2 * k + 4) ^ 2) N)
      atTop (𝓝 (mathieuCFHead q (mathieuB (2 * n + 2) q) (mathieuB (2 * n + 2) q - 4)
        (fun _ => 1) (fun k => (2 * k + 4) ^ 2) n)) := by
  sorry

/-- **DLMF 28.6.20**: the radii of convergence `ρ_n^{(j)}` of the power series of `a_{2n}`
(`j = 1`), `b_{2n+2}` (`j = 2`), `a_{2n+1}` and `b_{2n+1}` (`j = 3`) satisfy
`liminf ρ_n^{(j)}/n² ≥ k k' K(k)²`, where `k ∈ (0, 1)` is the root of `2E(k) = K(k)` and
`k' = √(1 - k²)`. Stated as: for every `c < k k' K(k)²`, for all large `n` each of these
eigenvalues extends analytically from the real interval `(-cn², cn²)` to the disc `|q| < cn²`. -/
@[dlmf 28.6.E20]
theorem mathieu_radius_liminf {k : ℝ} (hk : k ∈ Ioo (0 : ℝ) 1)
    (hEK : 2 * DLMF.EllipticIntegrals.compEllIntEk k = DLMF.JacobiElliptic.compEllIntKk k)
    {c : ℝ} (hc : c < k * Real.sqrt (1 - k ^ 2) * (DLMF.JacobiElliptic.compEllIntKk k).re ^ 2) :
    ∀ᶠ n : ℕ in atTop, ∀ e : ℕ → ℝ → ℝ, e ∈ ({fun n => mathieuA (2 * n),
        fun n => mathieuB (2 * n + 2), fun n => mathieuA (2 * n + 1),
        fun n => mathieuB (2 * n + 1)} : Set (ℕ → ℝ → ℝ)) →
      ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 (c * n ^ 2)) ∧
        ∀ q : ℝ, |q| < c * n ^ 2 → F q = e n q := by
  sorry

/-! ### Functions `ce_n`, `se_n` (§28.6(ii)) -/

/-- **DLMF 28.6.21**: `2^{1/2} ce₀(z, q) = 1 - (q/2) cos 2z + (q²/32)(cos 4z - 2)
- (q³/128)((1/9) cos 6z - 11 cos 2z) + O(q⁴)`. -/
@[dlmf 28.6.E21]
theorem mathieuCe_zero_small_q (z : ℂ) :
    (fun q : ℝ => (Real.sqrt 2 : ℂ) * mathieuCe 0 z q - (1 - q / 2 * Complex.cos (2 * z) +
      q ^ 2 / 32 * (Complex.cos (4 * z) - 2) -
      q ^ 3 / 128 * (1 / 9 * Complex.cos (6 * z) - 11 * Complex.cos (2 * z)))) =O[𝓝 0]
      (fun q => q ^ 4) := by
  sorry

/-- **DLMF 28.6.22**: `ce₁(z, q) = cos z - (q/8) cos 3z + (q²/128)((2/3) cos 5z - 2 cos 3z - cos z)
- (q³/1024)((1/9) cos 7z - (8/9) cos 5z - (1/3) cos 3z + 2 cos z) + O(q⁴)`. -/
@[dlmf 28.6.E22]
theorem mathieuCe_one_small_q (z : ℂ) :
    (fun q : ℝ => mathieuCe 1 z q - (Complex.cos z - q / 8 * Complex.cos (3 * z) +
      q ^ 2 / 128 * (2 / 3 * Complex.cos (5 * z) - 2 * Complex.cos (3 * z) - Complex.cos z) -
      q ^ 3 / 1024 * (1 / 9 * Complex.cos (7 * z) - 8 / 9 * Complex.cos (5 * z) -
        1 / 3 * Complex.cos (3 * z) + 2 * Complex.cos z))) =O[𝓝 0] (fun q => q ^ 4) := by
  sorry

/-- **DLMF 28.6.23**: `se₁(z, q) = sin z - (q/8) sin 3z + (q²/128)((2/3) sin 5z + 2 sin 3z - sin z)
- (q³/1024)((1/9) sin 7z + (8/9) sin 5z - (1/3) sin 3z - 2 sin z) + O(q⁴)`. -/
@[dlmf 28.6.E23]
theorem mathieuSe_one_small_q (z : ℂ) :
    (fun q : ℝ => mathieuSe 1 z q - (Complex.sin z - q / 8 * Complex.sin (3 * z) +
      q ^ 2 / 128 * (2 / 3 * Complex.sin (5 * z) + 2 * Complex.sin (3 * z) - Complex.sin z) -
      q ^ 3 / 1024 * (1 / 9 * Complex.sin (7 * z) + 8 / 9 * Complex.sin (5 * z) -
        1 / 3 * Complex.sin (3 * z) - 2 * Complex.sin z))) =O[𝓝 0] (fun q => q ^ 4) := by
  sorry

/-- **DLMF 28.6.24**: `ce₂(z, q) = cos 2z - (q/4)((1/3) cos 4z - 1)
+ (q²/128)((1/3) cos 6z - (76/9) cos 2z) + O(q³)`. -/
@[dlmf 28.6.E24]
theorem mathieuCe_two_small_q (z : ℂ) :
    (fun q : ℝ => mathieuCe 2 z q - (Complex.cos (2 * z) -
      q / 4 * (1 / 3 * Complex.cos (4 * z) - 1) +
      q ^ 2 / 128 * (1 / 3 * Complex.cos (6 * z) - 76 / 9 * Complex.cos (2 * z)))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  sorry

/-- **DLMF 28.6.25**: `se₂(z, q) = sin 2z - (q/12) sin 4z + (q²/128)((1/3) sin 6z - (4/9) sin 2z)
+ O(q³)`. -/
@[dlmf 28.6.E25]
theorem mathieuSe_two_small_q (z : ℂ) :
    (fun q : ℝ => mathieuSe 2 z q - (Complex.sin (2 * z) - q / 12 * Complex.sin (4 * z) +
      q ^ 2 / 128 * (1 / 3 * Complex.sin (6 * z) - 4 / 9 * Complex.sin (2 * z)))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  sorry

/-- **DLMF 28.6.26**: for `m ≥ 3`, `ce_m(z, q) = cos mz - (q/4)(cos(m+2)z/(m+1) - cos(m-2)z/(m-1))
+ (q²/32)(cos(m+4)z/((m+1)(m+2)) + cos(m-4)z/((m-1)(m-2)) - 2(m²+1) cos mz/(m²-1)²) + O(q³)`. -/
@[dlmf 28.6.E26]
theorem mathieuCe_small_q {m : ℕ} (hm : 3 ≤ m) (z : ℂ) :
    (fun q : ℝ => mathieuCe m z q - (Complex.cos (m * z) -
      q / 4 * (Complex.cos ((m + 2) * z) / (m + 1) - Complex.cos ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.cos ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.cos ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.cos (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  sorry

/-- **DLMF §28.6(ii)**: for `m ≥ 3` the expansion of `se_m(z, q)` is 28.6.26 with `cos` replaced
by `sin` everywhere. -/
@[dlmf 28.6.ii]
theorem mathieuSe_small_q {m : ℕ} (hm : 3 ≤ m) (z : ℂ) :
    (fun q : ℝ => mathieuSe m z q - (Complex.sin (m * z) -
      q / 4 * (Complex.sin ((m + 2) * z) / (m + 1) - Complex.sin ((m - 2) * z) / (m - 1)) +
      q ^ 2 / 32 * (Complex.sin ((m + 4) * z) / ((m + 1) * (m + 2)) +
        Complex.sin ((m - 4) * z) / ((m - 1) * (m - 2)) -
        2 * ((m : ℂ) ^ 2 + 1) * Complex.sin (m * z) / ((m : ℂ) ^ 2 - 1) ^ 2))) =O[𝓝 0]
      (fun q => q ^ 3) := by
  sorry

/-- **Radii of convergence** (DLMF §28.6(ii)): the power series in `q` of `ce_n(z, q)` (for each
fixed `z`) has the same radius of convergence as that of `a_n(q)`; stated as: `a_n` extends
analytically from `(-r, r)` to the disc `|q| < r` iff, for every `z`, `q ↦ ce_n(z, q)` does. -/
@[dlmf 28.6.ii]
theorem mathieuCe_radius_eq (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 r) ∧
        ∀ q : ℝ, |q| < r → F q = mathieuA n q) ↔
      ∀ z : ℂ, ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.ball 0 r) ∧
        ∀ q : ℝ, |q| < r → G q = mathieuCe n z q := by
  sorry

/-- **Radii of convergence** (DLMF §28.6(ii)) for `se_n` and `b_n`, `n ≥ 1`. -/
@[dlmf 28.6.ii]
theorem mathieuSe_radius_eq {n : ℕ} (hn : n ≠ 0) {r : ℝ} (hr : 0 < r) :
    (∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 r) ∧
        ∀ q : ℝ, |q| < r → F q = mathieuB n q) ↔
      ∀ z : ℂ, ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.ball 0 r) ∧
        ∀ q : ℝ, |q| < r → G q = mathieuSe n z q := by
  sorry

end DLMF.Mathieu
