/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.Gamma.Polygamma

/-!
# Ramanujan series and unit-argument digamma evaluations

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), Chapter 9,
(9.2)–(9.5), (9.29)–(9.40). A conditionally convergent alternating series
is stated as convergence of natural-order partial sums.
-/

@[expose] public noncomputable section
open Complex Filter Finset
open scoped Nat Topology Real
namespace DLMF.Hypergeometric

/-- Product identity in Ramanujan's letter, Rao–Lakshminarayanan (9.2),
synopsis RL-9.01. -/
theorem hasSum_zeroF2_mul_neg (z : ℂ) :
    HasSum (fun n : ℕ => ((3 * n).factorial : ℂ) /
      ((n.factorial : ℂ) ^ 3 * ((2 * n).factorial : ℂ) ^ 3) * (-z ^ 2) ^ n)
      (generalizedHypergeometric ∅ {1, 1} z * generalizedHypergeometric ∅ {1, 1} (-z)) := by
  sorry

/-- The ordinary alternating inverse-π series, Rao–Lakshminarayanan (9.3),
synopsis RL-9.01. Its summands are not absolutely summable. -/
theorem tendsto_sum_ramanujan_half_cubed :
    Tendsto (fun N : ℕ => ∑ n ∈ range N,
      (-1 : ℂ) ^ n * (4 * n + 1) * pochhammer (1 / 2) n ^ 3 /
        (n.factorial : ℂ) ^ 3) atTop (𝓝 (2 / (Real.pi : ℂ))) := by
  sorry

/-- Absolute convergence of the quarter-parameter letter identity,
Rao–Lakshminarayanan (9.4), synopsis RL-9.01. -/
theorem hasSum_ramanujan_quarter_fourth :
    HasSum (fun n : ℕ => (8 * n + 1 : ℂ) * pochhammer (1 / 4) n ^ 4 /
      (n.factorial : ℂ) ^ 4)
      ((2 : ℂ) ^ (3 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (3 / 4) ^ 2)) := by
  sorry

/-- The fifth-power letter identity, Rao–Lakshminarayanan (9.5), synopsis RL-9.01. -/
theorem hasSum_ramanujan_half_fifth :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n * (4 * n + 1) * pochhammer (1 / 2) n ^ 5 /
      (n.factorial : ℂ) ^ 5) (2 / Gamma (3 / 4) ^ 4) := by
  sorry

/-- The digamma evaluation of Entry 43, Example 7, Rao–Lakshminarayanan
(9.29)–(9.31), synopsis RL-9.06. The literal Gamma quotient is restricted
to its regular locus; exceptional values are stated separately. -/
theorem generalizedHypergeometric_half_repeated_digamma {x : ℂ} (hx : x.re < 2)
    (h₁ : ∀ n : ℕ, 1 - x ≠ -n) (h₂ : ∀ n : ℕ, 3 / 2 - x ≠ -n) :
    generalizedHypergeometric {x, 1 / 2, 1 / 2} {3 / 2, 3 / 2} 1 =
      Real.sqrt Real.pi * Gamma (1 - x) / (4 * Gamma (3 / 2 - x)) *
        (digamma (3 / 2 - x) - digamma (1 / 2)) := by
  sorry

/-- The labelled Rao–Vanden Berghe–Krattenthaler theorem,
Rao–Lakshminarayanan (9.32), p. 9-10, synopsis RL-9.07. -/
theorem generalizedHypergeometric_repeated_parameter_digamma (N : ℕ) (a x : ℂ)
    (ha : ∀ k : ℕ, a ≠ -k) (hx : x.re < N + 2)
    (hxΓ : ∀ k : ℕ, 1 - x ≠ -k)
    (hax : ∀ k : ℕ, a - x + 1 ≠ -k) :
    generalizedHypergeometric {a, a, x} {a + 1, a + N + 1} 1 =
      a * Gamma (a + N + 1) * Gamma (1 - x) /
        (N.factorial * Gamma (a - x + 1)) *
        (digamma (a - x + 1) - digamma a - digamma (N + 1) -
          Real.eulerMascheroniConstant -
          ∑ k ∈ Icc 1 N, pochhammer a k * pochhammer (-(N : ℂ)) k /
            (k * k.factorial * pochhammer (a - x + 1) k)) := by
  sorry

/-- The coalescing-parameter limit used in the digamma evaluation,
Rao–Lakshminarayanan (9.34)–(9.39), synopsis RL-9.08. -/
theorem tendsto_generalizedHypergeometric_coalescing_upper (N : ℕ) (a x : ℂ)
    (ha : ∀ k : ℕ, a ≠ -k) (hx : x.re < N + 2) :
    Tendsto (fun ε : ℂ => generalizedHypergeometric {a, a - ε, x}
      {1 + a - ε, 1 + a - ε + N} 1) (𝓝 0)
      (𝓝 (generalizedHypergeometric {a, a, x} {1 + a, 1 + a + N} 1)) := by
  sorry

/-- The removable `a=0` member of the Rao–Vanden Berghe–Krattenthaler
family, Rao–Lakshminarayanan (9.32), synopsis RL-9.07. The limit is taken of
the whole hypergeometric expression, without evaluating a singular digamma factor. -/
theorem tendsto_generalizedHypergeometric_repeated_upper_zero (N : ℕ) {x : ℂ}
    (hx : x.re < N + 2) :
    Tendsto (fun a : ℂ => generalizedHypergeometric {a, a, x}
      {1 + a, 1 + a + N} 1) (𝓝 0) (𝓝 1) := by
  sorry

/-- The coalescing-parameter limit is locally uniform in the remaining parameters,
Rao–Lakshminarayanan (9.34)–(9.39), synopsis RL-9.08. -/
theorem tendstoLocallyUniformlyOn_generalizedHypergeometric_coalescing_upper (N : ℕ) :
    TendstoLocallyUniformlyOn
      (fun ε (p : ℂ × ℂ) => generalizedHypergeometric {p.1, p.1 - ε, p.2}
        {1 + p.1 - ε, 1 + p.1 - ε + N} 1)
      (fun p : ℂ × ℂ => generalizedHypergeometric {p.1, p.1, p.2}
        {1 + p.1, 1 + p.1 + N} 1) (𝓝 0)
      {p | p.2.re < N + 2 ∧ ∀ k : ℕ, p.1 ≠ -(k : ℂ)} := by
  sorry

/-- Removable value at `x=1`, Rao–Lakshminarayanan (9.39), synopsis RL-9.09. -/
theorem generalizedHypergeometric_half_repeated_one :
    generalizedHypergeometric {1, 1 / 2, 1 / 2} {3 / 2, 3 / 2} 1 = Real.pi ^ 2 / 8 := by
  sorry

/-- Removable value at `x=3/2`, Rao–Lakshminarayanan (9.40), synopsis RL-9.09. -/
theorem generalizedHypergeometric_half_repeated_three_halves :
    generalizedHypergeometric {3 / 2, 1 / 2, 1 / 2} {3 / 2, 3 / 2} 1 = Real.pi / 2 := by
  sorry

/-- Terminating odd harmonic evaluation, Rao–Lakshminarayanan (9.39)–(9.40),
synopsis RL-9.09. -/
theorem generalizedHypergeometric_half_repeated_neg_nat (k : ℕ) :
    generalizedHypergeometricTruncated k {-(k : ℂ), 1 / 2, 1 / 2} {3 / 2, 3 / 2} 1 =
      Real.sqrt Real.pi * Gamma (k + 1) / (2 * Gamma (k + 3 / 2)) *
        ∑ j ∈ Icc 1 (k + 1), (2 * (j : ℂ) - 1)⁻¹ := by
  sorry

end DLMF.Hypergeometric
