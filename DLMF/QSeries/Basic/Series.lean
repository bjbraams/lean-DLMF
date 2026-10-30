/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic.Pochhammer

/-!
# Integer shifted factorials and basic q-series
-/

@[expose] public noncomputable section

open Complex Finset Filter
open scoped Real Topology

namespace DLMF.QSeries

/-- The integer-index q-Pochhammer symbol, AAR (10.5.2). -/
def qPochhammerInt (a q : ℂ) : ℤ → ℂ
  | .ofNat n => qPochhammer a q n
  | .negSucc n => (qPochhammer (a * q ^ (-(n + 1 : ℤ))) q (n + 1))⁻¹

/-- Basic hypergeometric series `ᵣφₛ` with `r = s + 1` (AAR §10.9). -/
def basicHG (a b : List ℂ) (q z : ℂ) : ℂ :=
  ∑' n : ℕ,
    (a.map fun ai => qPochhammer ai q n).prod /
        ((b.map fun bi => qPochhammer bi q n).prod * qPochhammer q q n) * z ^ n

/-- The Laurent form of the `q`-ultraspherical polynomials (AAR (10.11.1)),
with `x = exp(iθ)` corresponding to the polynomial argument `cos θ`. -/
@[dlmf 18.28.E13]
def qGegenbauer (beta q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    qPochhammer beta q k * qPochhammer beta q (n - k) /
        (qPochhammer q q k * qPochhammer q q (n - k)) * x ^ ((n : ℤ) - 2 * k)

namespace TripleProduct

/-- The exponent `n(n-1)/2` as an integer. -/
def tri (n : ℤ) : ℤ := n * (n - 1) / 2

/-- The summand `(-1)^n q^{n(n-1)/2} z^n` of the triple product. -/
def term (q z : ℂ) (n : ℤ) : ℂ := (-1 : ℂ) ^ n * q ^ tri n * z ^ n

/-- `∏_{j<k} (1 - r^{j+1})⁻¹`, a bound for `‖[n k]_q‖` with `r = ‖q‖`. -/
def dprod (r : ℝ) (k : ℕ) : ℝ := ∏ j ∈ range k, (1 - r ^ (j + 1))⁻¹

end TripleProduct

end DLMF.QSeries
