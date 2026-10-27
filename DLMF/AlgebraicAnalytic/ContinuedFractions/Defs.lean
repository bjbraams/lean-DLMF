/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.ContinuedFraction.Convergence

/-!
# Continued fractions: definitions (DLMF §1.12)

DLMF writes `C = b₀ + a₁/(b₁ + a₂/(b₂ + ⋯))` with partial numerators `a_n` (`n ≥ 1`) and partial
denominators `b_n` (`n ≥ 0`). Mathlib's `GenContFract K` is `h + a₀'/(b₀' + a₁'/(b₁' + ⋯))` with
pairs indexed from `0`, and `GenContFract.cfConv_ofFun h a b` (DLMFMathlib) builds it from two
sequences. `contFrac a b` is DLMF's fraction in DLMF's indexing (the value `a 0` is unused):

* `(contFrac a b).nums n = A_n`, `(contFrac a b).dens n = B_n` (the canonical numerators and
  denominators of 1.12.4–1.12.6), and `(contFrac a b).convs n = A_n/B_n`;
* `(contFrac a b).convs' n` is the nested finite fraction `b₀ + a₁/(b₁ + ⋯ + a_n/b_n)`;
  with Lean's `x / 0 = 0`, it equals `A_n/B_n` when its nested denominators do not vanish
  (`DLMF.AlgebraicAnalytic.contFrac_convs'_eq_convs`);
* `(contFrac a b).contsAux 0 = ⟨1, 0⟩ = ⟨A_{-1}, B_{-1}⟩`.

Further definitions: the nested tails `contFracTail`, the approximants `C_n(w)` of 1.12.20
(`contFracApprox`), equivalence and contraction of continued fractions, convergence, and the
elements of the even and odd parts (1.12.23–1.12.24).
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace DLMF.AlgebraicAnalytic

variable {K : Type*}

/-- DLMF 1.12.1–1.12.3: the continued fraction `b₀ + a₁/(b₁ + a₂/(b₂ + ⋯))`, in DLMF's
indexing (partial numerators `a n`, `n ≥ 1`; partial denominators `b n`, `n ≥ 0`; the value
`a 0` is not used). DLMF assumes `a_n ≠ 0`; statements carry this hypothesis where needed. -/
@[dlmf 1.12.E1, dlmf 1.12.E2, dlmf 1.12.E3]
def contFrac [DivisionRing K] (a b : ℕ → K) : GenContFract K :=
  GenContFract.cfConv_ofFun (b 0) (fun k => a (k + 1)) (fun k => b (k + 1))

/-- The `k`-th nested tail `b_k + a_{k+1}/(b_{k+1} + ⋯ + a_n/b_n)` of the `n`-th approximant,
the nested finite fraction of the shifted sequences. The nested form of the `n`-th approximant
is meaningful (no division by zero) when the tails with `1 ≤ k ≤ n` do not vanish. -/
def contFracTail [DivisionRing K] (a b : ℕ → K) (k n : ℕ) : K :=
  (contFrac (fun j => a (j + k)) (fun j => b (j + k))).convs' (n - k)

/-- DLMF 1.12.20: the approximant `C_n(w) = b₀ + a₁/(b₁ + ⋯ + a_n/(b_n + w))`, the nested
fraction with `b_n` replaced by `b_n + w`. -/
@[dlmf 1.12.E20]
def contFracApprox [DivisionRing K] (a b : ℕ → K) (n : ℕ) (w : K) : K :=
  (contFrac a (Function.update b n (b n + w))).convs' n

/-- DLMF §1.12(ii): two continued fractions are **equivalent** if they have the same
convergents. -/
@[dlmf 1.12.ii]
def ContFracEquiv [DivisionRing K] (a b a' b' : ℕ → K) : Prop :=
  ∀ n, (contFrac a b).convs n = (contFrac a' b').convs n

/-- DLMF 1.12.17: the factors `d_n` of the equivalence transformation to unit partial numerators,
`d₀ = 1`, `d_n = 1/(a_n d_{n-1})`, so that `d_n d_{n-1} a_n = 1`
(`d₁ = 1/a₁`, `d₂ = a₁/a₂`, `d₃ = a₂/(a₁a₃)`, `d₄ = a₁a₃/(a₂a₄)`, …). -/
@[dlmf 1.12.E17]
def contFracUnitFactor [DivisionRing K] (a : ℕ → K) : ℕ → K
  | 0 => 1
  | n + 1 => 1 / (a (n + 1) * contFracUnitFactor a n)

/-- DLMF §1.12(iv): `C'` is a **contraction** of `C` (and `C` an extension of `C'`) if the

convergents of `C'` form a subsequence of those of `C`. -/
@[dlmf 1.12.iv]
def IsContraction [DivisionRing K] (C' C : GenContFract K) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, C'.convs n = C.convs (φ n)

/-- DLMF §1.12(v): a continued fraction **converges** if its convergents `C_n` tend to a finite
limit. -/
@[dlmf 1.12.v]
def ContFracConverges [NormedField K] (a b : ℕ → K) : Prop :=
  ∃ C, Tendsto (contFrac a b).convs atTop (𝓝 C)

/-- DLMF 1.12.23: the partial numerators `a'_k` of the even part,
`a'₁ = a₁b₂`, `a'₂ = -a₂a₃b₄`, `a'_k = -a_{2k-2}a_{2k-1}b_{2k-4}b_{2k}` (`k ≥ 3`). -/
@[dlmf 1.12.E23]
def evenPartA [Ring K] (a b : ℕ → K) : ℕ → K
  | 0 => 0
  | 1 => a 1 * b 2
  | 2 => -(a 2 * a 3 * b 4)
  | k + 3 => -(a (2 * k + 4) * a (2 * k + 5) * b (2 * k + 2) * b (2 * k + 6))

/-- DLMF 1.12.23: the partial denominators `b'_k` of the even part, `b'₀ = b₀`,
`b'₁ = a₂ + b₁b₂`, `b'_k = a_{2k-1}b_{2k} + b_{2k-2}(a_{2k} + b_{2k-1}b_{2k})` (`k ≥ 2`). -/
@[dlmf 1.12.E23]
def evenPartB [Ring K] (a b : ℕ → K) : ℕ → K
  | 0 => b 0
  | 1 => a 2 + b 1 * b 2
  | k + 2 => a (2 * k + 3) * b (2 * k + 4) + b (2 * k + 2) * (a (2 * k + 4) +
      b (2 * k + 3) * b (2 * k + 4))

/-- DLMF 1.12.24: the partial numerators `a'_k` of the odd part, `a'₁ = -a₁a₂b₃/b₁`,
`a'_k = -a_{2k-1}a_{2k}b_{2k-3}b_{2k+1}` (`k ≥ 2`). -/
@[dlmf 1.12.E24]
def oddPartA [DivisionRing K] (a b : ℕ → K) : ℕ → K
  | 0 => 0
  | 1 => -(a 1 * a 2 * b 3 / b 1)
  | k + 2 => -(a (2 * k + 3) * a (2 * k + 4) * b (2 * k + 1) * b (2 * k + 5))

/-- DLMF 1.12.24: the partial denominators `b'_k` of the odd part, `b'₀ = (a₁ + b₀b₁)/b₁`,
`b'_k = a_{2k}b_{2k+1} + b_{2k-1}(a_{2k+1} + b_{2k}b_{2k+1})` (`k ≥ 1`). -/
@[dlmf 1.12.E24]
def oddPartB [DivisionRing K] (a b : ℕ → K) : ℕ → K
  | 0 => (a 1 + b 0 * b 1) / b 1
  | k + 1 => a (2 * k + 2) * b (2 * k + 3) + b (2 * k + 1) * (a (2 * k + 3) +
      b (2 * k + 2) * b (2 * k + 3))

end DLMF.AlgebraicAnalytic
