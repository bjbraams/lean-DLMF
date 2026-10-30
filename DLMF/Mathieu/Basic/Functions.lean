/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Basic.Spectral

/-!
# Normalized Mathieu functions and their Fourier coefficients
-/

@[expose] public noncomputable section

open Complex Set Filter
open scoped Topology Real Classical

namespace DLMF.Mathieu

/-! ### Eigenfunctions `ce_n`, `se_n` (§28.2(vi)) -/

/-- The positive normalizing factor `ce_n(0, q) = (π / ∫₀^{2π} w_I(x; a_n(q), q)² dx)^{1/2}`
(DLMF 28.2.30 together with 28.2.38), real `q`. -/
def mathieuCeZero (n : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖mathieuWI (mathieuA n q) q x‖ ^ 2)

/-- The positive normalizing factor `se_n'(0, q) = (π / ∫₀^{2π} w_II(x; b_n(q), q)² dx)^{1/2}`
(DLMF 28.2.30 together with 28.2.39), real `q`. -/
def mathieuSeDerivZero (n : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖mathieuWII (mathieuB n q) q x‖ ^ 2)

/-- The **Mathieu function** `ce_n(z, q)` (DLMF Table 28.2.2, 28.2.30, 28.2.38), real `q`,
complex `z`, `n = 0, 1, 2, …`: the even eigenfunction for `a_n(q)`,
`ce_n(z, q) = ce_n(0, q) w_I(z; a_n(q), q)`, normalized by `∫₀^{2π} ce_n² = π`, with
`ce_n(0, q) > 0` (DLMF's sign convention "by continuity from `q = 0`"). -/
@[dlmf 28.2.T2]
def mathieuCe (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  (mathieuCeZero n q : ℂ) * mathieuWI (mathieuA n q) q z

/-- The **Mathieu function** `se_n(z, q)` (DLMF Table 28.2.2, 28.2.30, 28.2.39), real `q`,
complex `z`, `n = 1, 2, …`: the odd eigenfunction for `b_n(q)`,
`se_n(z, q) = se_n'(0, q) w_II(z; b_n(q), q)`, normalized by `∫₀^{2π} se_n² = π`, with
`se_n'(0, q) > 0`. (`n = 0` gives a junk value.) -/
@[dlmf 28.2.T2]
def mathieuSe (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  (mathieuSeDerivZero n q : ℂ) * mathieuWII (mathieuB n q) q z

/-! ### Second solutions `fe_n`, `ge_n` (§28.5) -/

/-- The coefficient `μ` of the secular part of `w_II(z; a_n(q), q) = μ z w_I(z) + u(z)` with
`u` (anti)periodic: `μ = w_I(π) w_II(π) / π` (DLMF §28.5; uses 28.2.8–28.2.9). -/
def mathieuFeMu (n : ℕ) (q : ℝ) : ℂ :=
  mathieuWI (mathieuA n q) q π * mathieuWII (mathieuA n q) q π / π

/-- The (anti)periodic odd part `u(z) = w_II(z) - μ z w_I(z)` at `a = a_n(q)` (DLMF §28.5). -/
def mathieuFeU (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  mathieuWII (mathieuA n q) q z - mathieuFeMu n q * z * mathieuWI (mathieuA n q) q z

/-- The coefficient `μ = w_I'(π) w_II'(π) / π` of the secular part of
`w_I(z; b_n(q), q) = μ z w_II(z) + u(z)` (DLMF §28.5). -/
def mathieuGeMu (n : ℕ) (q : ℝ) : ℂ :=
  deriv (mathieuWI (mathieuB n q) q) π * deriv (mathieuWII (mathieuB n q) q) π / π

/-- The (anti)periodic even part `u(z) = w_I(z) - μ z w_II(z)` at `a = b_n(q)` (DLMF §28.5). -/
def mathieuGeU (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  mathieuWI (mathieuB n q) q z - mathieuGeMu n q * z * mathieuWII (mathieuB n q) q z

/-- The positive factor `fe_n'(0, q) = (π / ∫₀^{2π} u²)^{1/2}` (DLMF 28.5.5). -/
def mathieuFeDerivZero (n : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖mathieuFeU n x q‖ ^ 2)

/-- The positive factor `ge_n(0, q) = (π / ∫₀^{2π} u²)^{1/2}` (DLMF 28.5.5). -/
def mathieuGeZero (n : ℕ) (q : ℝ) : ℝ :=
  Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖mathieuGeU n x q‖ ^ 2)

/-- The **second solution** `fe_n(z, q)` (DLMF 28.5.1, 28.5.5, 28.5.7), real `q`, `n ≥ 0`: the
odd solution of Mathieu's equation with `a = a_n(q)`, `fe_n = fe_n'(0, q) w_II(z; a_n(q), q)`,
normalized by 28.5.5 with `fe_n'(0, q) > 0`; `fe_0(z, 0) = z` (28.5.7). -/
@[dlmf 28.5.E1]
def mathieuFe (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  if n = 0 ∧ q = 0 then z else (mathieuFeDerivZero n q : ℂ) * mathieuWII (mathieuA n q) q z

/-- The **second solution** `ge_n(z, q)` (DLMF 28.5.2, 28.5.5, 28.5.7), real `q`, `n ≥ 1`: the
even solution with `a = b_n(q)`, `ge_n = ge_n(0, q) w_I(z; b_n(q), q)`, normalized by 28.5.5
with `ge_n(0, q) > 0`. -/
@[dlmf 28.5.E2]
def mathieuGe (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  (mathieuGeZero n q : ℂ) * mathieuWI (mathieuB n q) q z

/-- The factor `C_n(q)` of DLMF 28.5.1: `C_n = fe_n'(0) μ / ce_n(0)`, so that
`fe_n = C_n (z ce_n + f_n)`; `C_0(0) = √2`. Vanishes at `q = 0` for `n ≥ 1`. -/
@[dlmf 28.5.E1]
def mathieuFeC (n : ℕ) (q : ℝ) : ℂ :=
  if n = 0 ∧ q = 0 then Real.sqrt 2 else
    (mathieuFeDerivZero n q : ℂ) * mathieuFeMu n q / mathieuCeZero n q

/-- The factor `S_n(q)` of DLMF 28.5.2: `S_n = ge_n(0) μ / se_n'(0)`, so that
`ge_n = S_n (z se_n + g_n)`. Vanishes at `q = 0`. -/
@[dlmf 28.5.E2]
def mathieuGeS (n : ℕ) (q : ℝ) : ℂ :=
  (mathieuGeZero n q : ℂ) * mathieuGeMu n q / mathieuSeDerivZero n q

/-- The periodic or antiperiodic odd function `f_n(z, q) = fe_n / C_n - z ce_n` of DLMF 28.5.1
(meaningful for `C_n(q) ≠ 0`, i.e. `q ≠ 0` or `n = 0`). -/
@[dlmf 28.5.E3]
def mathieuFeF (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  mathieuFe n z q / mathieuFeC n q - z * mathieuCe n z q

/-- The periodic or antiperiodic even function `g_n(z, q) = ge_n / S_n - z se_n` of DLMF 28.5.2
(meaningful for `q ≠ 0`). -/
@[dlmf 28.5.E4]
def mathieuGeG (n : ℕ) (z : ℂ) (q : ℝ) : ℂ :=
  mathieuGe n z q / mathieuGeS n q - z * mathieuSe n z q

/-! ### Fourier coefficients (§28.4) -/

/-- The **Fourier coefficient** `A^n_m(q)` of `ce_n(z, q) = ∑ₘ A^n_m(q) cos mz` (DLMF
28.4.1–28.4.2; only `m ≡ n (mod 2)` occur), real `q`:
`A^n_0 = (2π)⁻¹ ∫₀^{2π} ce_n`, `A^n_m = π⁻¹ ∫₀^{2π} ce_n(x) cos mx dx` for `m ≥ 1`. -/
@[dlmf 28.4.E1]
def mathieuFourierA (n m : ℕ) (q : ℝ) : ℂ :=
  (if m = 0 then 1 / (2 * π) else 1 / π : ℂ) *
    ∫ x in (0 : ℝ)..2 * π, mathieuCe n x q * Complex.cos (m * x)

/-- The **Fourier coefficient** `B^n_m(q)` of `se_n(z, q) = ∑ₘ B^n_m(q) sin mz` (DLMF
28.4.3–28.4.4), real `q`: `B^n_m = π⁻¹ ∫₀^{2π} se_n(x) sin mx dx`. -/
@[dlmf 28.4.E3]
def mathieuFourierB (n m : ℕ) (q : ℝ) : ℂ :=
  (1 / π : ℂ) * ∫ x in (0 : ℝ)..2 * π, mathieuSe n x q * Complex.sin (m * x)

end DLMF.Mathieu
