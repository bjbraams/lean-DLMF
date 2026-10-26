/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Truncated continued fractions for the Mathieu eigenvalues (DLMF 28.6.16–28.6.19)

Two auxiliary definitions used to state the continued-fraction equations 28.6.16–28.6.19:

* `mathieuCFTail q a s N = q²/(s₀ - a - q²/(s₁ - a - ⋯ - q²/(s_{N-1} - a)))`, the `N`-th
  truncation of the infinite continued fraction on the right-hand sides;
* `mathieuCFHead q a e₀ c s k`, the finite continued fraction on the left-hand sides, built from
  the innermost term `E₀ = e₀` by `E_{k+1} = a - s_k - c_k q²/E_k`.

Divisions are Lean's totalized division; the statements using these definitions carry the
needed nonvanishing hypotheses.
-/

@[expose] public noncomputable section

namespace DLMF.Mathieu

/-- The `N`-th truncation `q²/(s₀ - a - q²/(s₁ - a - ⋯ - q²/(s_{N-1} - a)))` of the infinite
continued fraction of DLMF 28.6.16–28.6.19 (`0` for `N = 0`). -/
def mathieuCFTail (q a : ℂ) (s : ℕ → ℂ) (N : ℕ) : ℂ :=
  (List.range N).foldr (fun k F => q ^ 2 / (s k - a - F)) 0

/-- The finite continued fraction of the left-hand sides of DLMF 28.6.16–28.6.19:
`E₀ = e₀`, `E_{k+1} = a - s_k - c_k q²/E_k`. -/
def mathieuCFHead (q a e₀ : ℂ) (c s : ℕ → ℂ) : ℕ → ℂ
  | 0 => e₀
  | k + 1 => a - s k - c k * q ^ 2 / mathieuCFHead q a e₀ c s k

end DLMF.Mathieu
