/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.EulerMaclaurin
public import DLMFMathlib.Analysis.BooleSummation
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Polynomial summation with local derivatives and signed remainders

Temme, *Special Functions* (1996), Theorems 1.1–1.5. Local derivative jets
retain one-sided endpoint derivatives; alternating tails use natural-order
partial sums and the top derivative is absolutely integrable.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Polynomial Finset
open scoped Nat Topology ContDiff

/-- Periodized Bernoulli functions have `n-2` continuous derivatives,
Temme §1.1, (1.16), synopsis TEM-01-05, corrected target TEM-E01. -/
theorem contDiff_periodicBernoulli {n : ℕ} (hn : 2 ≤ n) :
    ContDiff ℝ (n - 2) (periodicBernoulli n) := by
  sorry

/-- The derivative of a periodic Bernoulli function off the integers,
Temme (1.16), synopsis TEM-01-05. -/
theorem hasDerivAt_periodicBernoulli {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : ∀ m : ℤ, x ≠ m) :
    HasDerivAt (periodicBernoulli n) (n * periodicBernoulli (n - 1) x) x := by
  sorry

/-- The first periodized Bernoulli function has a downward jump of one,
Temme (1.16), synopsis TEM-01-05. -/
theorem tendsto_periodicBernoulli_one_sides (m : ℤ) :
    Tendsto (periodicBernoulli 1) (𝓝[<] (m : ℝ)) (𝓝 (1 / 2)) ∧
      Tendsto (periodicBernoulli 1) (𝓝[>] (m : ℝ)) (𝓝 (-1 / 2)) := by
  sorry

/-- Euler's antiperiodic extension has `n-1` continuous derivatives,
Temme §1.3, synopsis TEM-01-12, corrected target TEM-E02. -/
theorem contDiff_antiperiodicEuler {n : ℕ} (hn : 1 ≤ n) :
    ContDiff ℝ (n - 1) (antiperiodicEuler n) := by
  sorry

/-- Unit antiperiodicity, hence period two, of the Euler extension,
Temme §1.3, synopsis TEM-01-12, corrected target TEM-E02. -/
theorem antiperiodic_antiperiodicEuler (n : ℕ) :
    Function.Antiperiodic (antiperiodicEuler n) 1 := by
  intro x
  have hf : ⌊x + 1⌋ = ⌊x⌋ + (1 : ℤ) := by simp
  have hfract : Int.fract (x + 1) = Int.fract x := by simp
  simp only [antiperiodicEuler, hf, hfract, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0),
    zpow_one]
  ring

/-- One-cell Euler summation with one-sided endpoint derivatives,
Temme Theorem 1.1, p. 9, synopsis TEM-01-07; also Duverney Chapter 2,
Exercise 2.16, p. 51, synopsis DU-2.25. -/
theorem euler_summation_one_cell {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : ℕ → ℝ → E) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ∀ j ≤ k, ContinuousOn (F j) (Icc 0 1))
    (hderiv : ∀ j < k, ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (F j) (F (j + 1) x) (Icc 0 1) x) :
    F 0 1 = (∫ t : ℝ in (0 : ℝ)..1, F 0 t) +
      (∑ j ∈ Icc 1 k, ((-1 : ℝ) ^ j * (bernoulli j : ℝ) / j.factorial) •
        (F (j - 1) 1 - F (j - 1) 0)) +
      ((-1 : ℝ) ^ (k + 1) / k.factorial) •
        ∫ t : ℝ in (0 : ℝ)..1, bernoulliFun k t • F k t := by
  sorry

/-- One-cell Boole formula with the necessary alternating remainder sign,
Temme Theorem 1.4, p. 17, synopsis TEM-01-13, corrected target TEM-E05. -/
theorem boole_summation_one_cell {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : ℕ → ℝ → E) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ∀ j ≤ k, ContinuousOn (F j) (Icc 0 1))
    (hderiv : ∀ j < k, ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (F j) (F (j + 1) x) (Icc 0 1) x) :
    F 0 1 = (1 / 2 : ℝ) •
      (∑ j ∈ range k, (eulerFun j 1 / j.factorial) • (F j 1 + F j 0)) +
      ((-1 : ℝ) ^ (k + 1) / (2 * (k - 1).factorial)) •
        ∫ t : ℝ in (0 : ℝ)..1, eulerFun (k - 1) t • F k t := by
  sorry

/-- Infinite shifted Boole summation with absolute integrability of the top
 derivative, Temme Theorem 1.5, pp. 17–18, synopsis TEM-01-14, corrected TEM-E06. -/
theorem tendsto_boole_summation_shifted (F : ℕ → ℝ → ℝ) (m : ℤ)
    {h : ℝ} (hh : h ∈ Icc (0 : ℝ) 1) {k : ℕ} (hk : 1 ≤ k)
    (hcont : ∀ j ≤ k, ContinuousOn (F j) (Ici (m : ℝ)))
    (hderiv : ∀ j < k, ∀ x ∈ Ici (m : ℝ),
      HasDerivWithinAt (F j) (F (j + 1) x) (Ici (m : ℝ)) x)
    (hlim : ∀ j ≤ k, Tendsto (F j) atTop (𝓝 0))
    (hint : IntegrableOn (F k) (Ici (m : ℝ))) :
    Tendsto (fun N : ℕ => ∑ j ∈ range N, (-1 : ℝ) ^ j * F 0 (m + j + h)) atTop
      (𝓝 ((1 / 2 : ℝ) * (∑ r ∈ range k, eulerFun r h / r.factorial * F r m) +
        (1 / (2 * (k - 1).factorial : ℝ)) *
          ∫ t : ℝ in Ici (m : ℝ), antiperiodicEuler (k - 1) (m + h - t) * F k t)) := by
  sorry

/-- Euler–Maclaurin has an enveloping remainder for derivatives monotone to zero,
Temme Theorem 1.3, pp. 12–13, synopsis TEM-01-09. -/
theorem exists_eulerMaclaurin_remainder_factor (F : ℕ → ℝ → ℝ)
    (hcont : ∀ j, ContinuousOn (F j) (Ici 0))
    (hderiv : ∀ j, ∀ x ∈ Ici (0 : ℝ),
      HasDerivWithinAt (F j) (F (j + 1) x) (Ici 0) x)
    (hmono : ∀ j : ℕ, MonotoneOn (F j) (Ici 0) ∨ AntitoneOn (F j) (Ici 0))
    (hlim : ∀ j : ℕ, Tendsto (F j) atTop (𝓝 0))
    (k n : ℕ) (hn : 1 ≤ n) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      (∑ j ∈ range (n + 1), F 0 j) - (∫ t : ℝ in (0 : ℝ)..n, F 0 t) -
        (F 0 0 + F 0 n) / 2 -
        (∑ r ∈ range k, (bernoulli (2 * r + 2) : ℝ) / (2 * r + 2).factorial *
          (F (2 * r + 1) n - F (2 * r + 1) 0)) =
      θ * (bernoulli (2 * k + 2) : ℝ) / (2 * k + 2).factorial *
        (F (2 * k + 1) n - F (2 * k + 1) 0) := by
  sorry

/-- Euler–Maclaurin on an integer interval with one-sided endpoint derivative jets,
Temme Theorem 1.2, (1.19)–(1.21), synopsis TEM-01-08. -/
theorem sum_range_eulerMaclaurin_local {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : ℕ → ℝ → E) (m : ℤ) (n k : ℕ)
    (hcont : ∀ j ≤ 2 * k + 1, ContinuousOn (F j) (Icc (m : ℝ) (m + n)))
    (hderiv : ∀ j < 2 * k + 1, ∀ x ∈ Icc (m : ℝ) (m + n),
      HasDerivWithinAt (F j) (F (j + 1) x) (Icc (m : ℝ) (m + n)) x) :
    (∑ j ∈ range (n + 1), F 0 (m + j)) =
      (∫ t : ℝ in (m : ℝ)..(m + n), F 0 t) + (1 / 2 : ℝ) • (F 0 m + F 0 (m + n)) +
        (∑ r ∈ range k, ((bernoulli (2 * r + 2) : ℝ) / (2 * r + 2).factorial) •
          (F (2 * r + 1) (m + n) - F (2 * r + 1) m)) +
        ((2 * k + 1).factorial : ℝ)⁻¹ •
          ∫ t : ℝ in (m : ℝ)..(m + n), periodicBernoulli (2 * k + 1) t • F (2 * k + 1) t := by
  sorry

/-- Infinite Euler–Maclaurin with ordinary improper integrals, without requiring
absolute convergence of the tail integral, Temme (1.21), synopsis TEM-01-08. -/
theorem tendsto_sum_eulerMaclaurin_local {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (F : ℕ → ℝ → E) (m : ℤ) (k : ℕ) (I R : E)
    (hcont : ∀ j ≤ 2 * k + 1, ContinuousOn (F j) (Ici (m : ℝ)))
    (hderiv : ∀ j < 2 * k + 1, ∀ x ∈ Ici (m : ℝ),
      HasDerivWithinAt (F j) (F (j + 1) x) (Ici (m : ℝ)) x)
    (hlim : ∀ j ≤ 2 * k, Tendsto (F j) atTop (𝓝 0))
    (hI : Tendsto (fun n : ℕ => ∫ t : ℝ in (m : ℝ)..(m + n), F 0 t) atTop (𝓝 I))
    (hR : Tendsto (fun n : ℕ => ∫ t : ℝ in (m : ℝ)..(m + n),
      periodicBernoulli (2 * k + 1) t • F (2 * k + 1) t) atTop (𝓝 R)) :
    Tendsto (fun n : ℕ => ∑ j ∈ range (n + 1), F 0 (m + j)) atTop
      (𝓝 (I + (1 / 2 : ℝ) • F 0 m -
        (∑ r ∈ range k, ((bernoulli (2 * r + 2) : ℝ) / (2 * r + 2).factorial) •
          F (2 * r + 1) m) + ((2 * k + 1).factorial : ℝ)⁻¹ • R)) := by
  sorry

/-- The infinite-endpoint first-omitted-term form under monotonicity of every derivative,
Temme Theorem 1.3, synopsis TEM-01-09. -/
theorem exists_eulerMaclaurin_tail_remainder_factor (F : ℕ → ℝ → ℝ)
    (hcont : ∀ j, ContinuousOn (F j) (Ici 0))
    (hderiv : ∀ j, ∀ x ∈ Ici (0 : ℝ),
      HasDerivWithinAt (F j) (F (j + 1) x) (Ici 0) x)
    (hmono : ∀ j : ℕ, MonotoneOn (F j) (Ici 0) ∨ AntitoneOn (F j) (Ici 0))
    (hlim : ∀ j : ℕ, Tendsto (F j) atTop (𝓝 0)) (I S : ℝ)
    (hI : Tendsto (fun b : ℝ => ∫ t : ℝ in (0 : ℝ)..b, F 0 t) atTop (𝓝 I))
    (hS : Tendsto (fun n : ℕ => ∑ j ∈ range (n + 1), F 0 j) atTop (𝓝 S)) (k : ℕ) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      S - I - F 0 0 / 2 +
        (∑ r ∈ range k, (bernoulli (2 * r + 2) : ℝ) / (2 * r + 2).factorial *
          F (2 * r + 1) 0) =
      -θ * (bernoulli (2 * k + 2) : ℝ) / (2 * k + 2).factorial * F (2 * k + 1) 0 := by
  sorry

/-- The alternating odd-harmonic tail has an Euler-number expansion with an explicit
first-omitted-term bound, Temme §1.3, synopsis TEM-01-14. -/
theorem exists_alternating_odd_harmonic_remainder {n N : ℕ} (hn : 0 < n) (hN : 0 < N) :
    ∃ R : ℝ, |R| ≤ |(eulerNumber (2 * N) : ℝ)| / (2 * n : ℝ) ^ (2 * N + 1) ∧
      Tendsto (fun M : ℕ => 2 * ∑ j ∈ range M, (-1 : ℝ) ^ (n + j) / (2 * (n + j) + 1))
        atTop (𝓝 ((-1 : ℝ) ^ n *
          (∑ r ∈ range N, (eulerNumber (2 * r) : ℝ) / (2 * n : ℝ) ^ (2 * r + 1)) + R)) := by
  sorry
