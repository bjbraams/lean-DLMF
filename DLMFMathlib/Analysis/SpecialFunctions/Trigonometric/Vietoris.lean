/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Vietoris positivity and Szegő zero intervals

Andrews, Askey and Roy, *Special Functions*, §§7.3 and 7.5. Ordered partial sums
express the conditionally convergent infinite Vietoris series. The sine polynomial
in Szegő's theorem includes its leading frequency, correcting the printed lower index.
-/

@[expose] public section

open Finset Filter Set
open scoped Topology Real

noncomputable section

namespace Real

/-- Vietoris's paired coefficients `(1/2)_⌊n/2⌋ / ⌊n/2⌋!`.
Andrews–Askey–Roy, *Special Functions*, §7.3 (synopsis AAR-7.3.1–7.3.6). -/
def vietorisCoefficient (n : ℕ) : ℝ :=
  (ascPochhammer ℝ (n / 2)).eval (1 / 2) / (n / 2).factorial

/-- The finite rising-factorial formula for the paired coefficients. -/
theorem vietorisCoefficient_def (n : ℕ) :
    vietorisCoefficient n =
      (ascPochhammer ℝ (n / 2)).eval (1 / 2) / (n / 2).factorial := rfl

/-- The infinite Vietoris sine and cosine series have the same explicit value.
Andrews–Askey–Roy, *Special Functions*, Proposition 7.3.1, p. 372
(synopsis AAR-7.3.1–7.3.6). -/
theorem tendsto_sum_vietoris {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), vietorisCoefficient k * sin (k * θ))
      atTop (𝓝 (sqrt (cot (θ / 2) / 2))) ∧
    Tendsto (fun N => ∑ k ∈ Finset.range (N + 1), vietorisCoefficient k * cos (k * θ))
      atTop (𝓝 (sqrt (cot (θ / 2) / 2))) := by
  sorry

/-- The central-binomial strict Wallis bound used in Vietoris's proof.
Andrews–Askey–Roy, *Special Functions*, Proposition 7.3.2, p. 373
(synopsis AAR-7.3.1–7.3.6). -/
theorem centralBinom_lt_four_pow_div_sqrt_pi_mul {m : ℕ} (hm : 0 < m) :
    (Nat.choose (2 * m) m : ℝ) < 4 ^ m / sqrt (Real.pi * m) := by
  sorry

/-- Both finite Vietoris sums have the explicit common lower bound after multiplication
by `2 sin(θ/2)`. Andrews–Askey–Roy, *Special Functions*, Proposition 7.3.3, p. 373
(synopsis AAR-7.3.1–7.3.6). -/
theorem sqrt_sin_sub_le_vietoris_sums (N : ℕ) {θ : ℝ}
    (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    sqrt (sin θ) - 2 * vietorisCoefficient (N + 1) ≤
        2 * sin (θ / 2) * ∑ k ∈ Finset.range (N + 1), vietorisCoefficient k * sin (k * θ) ∧
    sqrt (sin θ) - 2 * vietorisCoefficient (N + 1) ≤
        2 * sin (θ / 2) * ∑ k ∈ Finset.range (N + 1), vietorisCoefficient k * cos (k * θ) := by
  sorry

/-- Strict Vietoris positivity in the open half-period.
Andrews–Askey–Roy, *Special Functions*, Theorem 7.3.4, p. 374
(synopsis AAR-7.3.1–7.3.6). -/
theorem vietoris_sums_pos {N : ℕ} (hN : 0 < N) {θ : ℝ}
    (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    0 < ∑ k ∈ Finset.range (N + 1), vietorisCoefficient k * sin (k * θ) ∧
    0 < ∑ k ∈ Finset.range (N + 1), vietorisCoefficient k * cos (k * θ) := by
  sorry

/-- The generalized monotone-coefficient Vietoris criterion.
Andrews–Askey–Roy, *Special Functions*, Theorem 7.3.5, p. 376
(synopsis AAR-7.3.1–7.3.6). -/
theorem trig_sums_pos_of_vietoris_coefficients {N : ℕ} (hN : 0 < N) (a : ℕ → ℝ)
    (ha : ∀ k ≤ N, 0 < a k) (hmono : AntitoneOn a (Set.Icc 0 N))
    (hpairs : ∀ k : ℕ, 0 < k → 2 * k ≤ N →
      (2 * k : ℝ) * a (2 * k) ≤ (2 * k - 1 : ℝ) * a (2 * k - 1))
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    0 < ∑ k ∈ Finset.range (N + 1), a k * sin (k * θ) ∧
    0 < ∑ k ∈ Finset.range (N + 1), a k * cos (k * θ) := by
  sorry

/-- Szegő's simple-zero intervals for monotone positive cosine and sine coefficients.
Andrews–Askey–Roy, *Special Functions*, Theorem 7.3.6, pp. 378–380
(synopsis AAR-7.3.1–7.3.6). The sine sum starts at zero as required by its leading
frequency and the number of zeros; see ERRATA-AAR.md. -/
theorem exists_trig_zeros_of_antitone_coefficients {N : ℕ} (hN : 0 < N)
    (a : ℕ → ℝ) (ha : ∀ k ≤ N, 0 < a k) (hmono : AntitoneOn a (Set.Icc 0 N))
    (hfirst : a 1 < a 0) :
    ∃ s : Fin N → ℝ, ∃ t : Fin (N - 1) → ℝ,
      StrictMono s ∧ StrictMono t ∧
      (∀ i, (s i ∈ Ioo 0 Real.pi) ∧
        (∑ j ∈ Finset.range (N + 1), a j * cos (((N - j : ℕ) : ℝ) * s i)) = 0 ∧
        deriv (fun θ => ∑ j ∈ Finset.range (N + 1),
          a j * cos (((N - j : ℕ) : ℝ) * θ)) (s i) ≠ 0 ∧
        ((i.val : ℝ) + 1 / 2) * Real.pi / (N + 1 / 2 : ℝ) < s i ∧
        s i < ((i.val : ℝ) + 3 / 2) * Real.pi / (N + 1 / 2 : ℝ)) ∧
      (∀ i, (t i ∈ Ioo 0 Real.pi) ∧
        (∑ j ∈ Finset.range N, a j * sin (((N - j : ℕ) : ℝ) * t i)) = 0 ∧
        deriv (fun θ => ∑ j ∈ Finset.range N,
          a j * sin (((N - j : ℕ) : ℝ) * θ)) (t i) ≠ 0 ∧
        ((i.val : ℝ) + 1) * Real.pi / (N + 1 / 2 : ℝ) < t i ∧
        t i < ((i.val : ℝ) + 2) * Real.pi / (N + 1 / 2 : ℝ)) ∧
      (∀ θ ∈ Ioo (0 : ℝ) Real.pi,
        (∑ j ∈ Finset.range (N + 1), a j * cos (((N - j : ℕ) : ℝ) * θ)) = 0 ↔
          ∃ i, θ = s i) ∧
      (∀ θ ∈ Ioo (0 : ℝ) Real.pi,
        (∑ j ∈ Finset.range N, a j * sin (((N - j : ℕ) : ℝ) * θ)) = 0 ↔
          ∃ i, θ = t i) := by
  sorry

/-- Szegő’s improved upper bounds under discrete convexity. Andrews–Askey–Roy,
*Special Functions*, Theorem 7.3.6 (synopsis AAR-7.3.1–7.3.6). -/
theorem exists_trig_zeros_of_convex_coefficients {N : ℕ} (hN : 2 ≤ N)
    (a : ℕ → ℝ) (ha : ∀ k ≤ N, 0 ≤ a k) (hmono : AntitoneOn a (Set.Icc 0 N))
    (hfirst : a 1 < a 0)
    (hstart : a 1 - a 2 < 2 * a 0 - a 1)
    (hconv : ∀ k : ℕ, 1 ≤ k → k + 2 ≤ N →
      a (k + 1) - a (k + 2) ≤ a k - a (k + 1))
    (hend : a N ≤ a (N - 1) - a N) :
    ∃ s : Fin N → ℝ, ∃ t : Fin (N - 1) → ℝ,
      StrictMono s ∧ StrictMono t ∧
      (∀ i, (s i ∈ Ioo 0 Real.pi) ∧
        (∑ j ∈ Finset.range (N + 1), a j * cos (((N - j : ℕ) : ℝ) * s i)) = 0 ∧
        deriv (fun θ => ∑ j ∈ Finset.range (N + 1),
          a j * cos (((N - j : ℕ) : ℝ) * θ)) (s i) ≠ 0 ∧
        ((i.val : ℝ) + 1 / 2) * Real.pi / (N + 1 / 2 : ℝ) < s i ∧
        s i < ((i.val : ℝ) + 1) * Real.pi / N) ∧
      (∀ i, (t i ∈ Ioo 0 Real.pi) ∧
        (∑ j ∈ Finset.range N, a j * sin (((N - j : ℕ) : ℝ) * t i)) = 0 ∧
        deriv (fun θ => ∑ j ∈ Finset.range N,
          a j * sin (((N - j : ℕ) : ℝ) * θ)) (t i) ≠ 0 ∧
        ((i.val : ℝ) + 1) * Real.pi / (N + 1 / 2 : ℝ) < t i ∧
        t i < ((i.val : ℝ) + 3 / 2) * Real.pi / N) ∧
      (∀ θ ∈ Ioo (0 : ℝ) Real.pi,
        (∑ j ∈ Finset.range (N + 1), a j * cos (((N - j : ℕ) : ℝ) * θ)) = 0 ↔
          ∃ i, θ = s i) ∧
      (∀ θ ∈ Ioo (0 : ℝ) Real.pi,
        (∑ j ∈ Finset.range N, a j * sin (((N - j : ℕ) : ℝ) * θ)) = 0 ↔
          ∃ i, θ = t i) := by
  sorry

/-- Turán's positivity-preserving shift from half-integer sine frequencies to ordinary
integer sine frequencies. Andrews–Askey–Roy, *Special Functions*, Theorem 7.5.1,
p. 384 (synopsis AAR-7.4.1–7.6.4). Absolute summability makes both displayed series ordinary
functions. -/
theorem tsum_sin_div_pos_of_tsum_half_sin_nonneg (a : ℕ → ℝ)
    (ha : Summable (fun j => |a j|)) (hne : ∃ j, a j ≠ 0)
    (hpositive : ∀ φ ∈ Icc (0 : ℝ) Real.pi,
      0 ≤ ∑' j, a j * sin (((j : ℝ) + 1 / 2) * φ))
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    0 < ∑' j, a j * sin (((j : ℝ) + 1) * θ) / (j + 1 : ℝ) := by
  sorry

end Real
