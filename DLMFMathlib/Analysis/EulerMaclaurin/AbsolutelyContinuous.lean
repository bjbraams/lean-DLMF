/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMFMathlib.Analysis.EulerMaclaurin
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Euler–Maclaurin with absolutely continuous highest antiderivative

Olver, *Asymptotics and Special Functions*, Chapter 8, §2,
pp. 284–287, synopsis O-8.03. Derivatives within the closed interval
retain endpoint data; the last derivative need only be integrable.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Real.EulerMaclaurin

/-- The even periodic-Bernoulli remainder, with Olver's omitted-endpoint-term
normalization. Olver, Chapter 8, §2, pp. 284–287. -/
def evenRemainder (f : ℝ → ℝ) (m : ℕ) (a n : ℤ) : ℝ :=
  ∫ x in (a : ℝ)..(n : ℝ),
    ((bernoulli (2 * m) : ℝ) - periodicBernoulli (2 * m) x) /
      (2 * m).factorial * iteratedDerivWithin (2 * m) f (Icc (a : ℝ) n) x

/-- The defining integral remainder. -/
theorem evenRemainder_def (f : ℝ → ℝ) (m : ℕ) (a n : ℤ) : evenRemainder f m a n =
    ∫ x in (a : ℝ)..(n : ℝ),
      ((bernoulli (2 * m) : ℝ) - periodicBernoulli (2 * m) x) /
        (2 * m).factorial * iteratedDerivWithin (2 * m) f (Icc (a : ℝ) n) x := rfl

/-- The exact finite Euler–Maclaurin identity under absolute continuity of the
last antiderivative. Olver, Chapter 8, §2, pp. 284–287. -/
theorem sum_Ico_eq_integral_add_evenRemainder {a n : ℤ} (han : a < n)
    {m : ℕ} (hm : 1 ≤ m) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (2 * m - 1) f (Icc (a : ℝ) n))
    (hac : AbsolutelyContinuousOnInterval
      (iteratedDerivWithin (2 * m - 1) f (Icc (a : ℝ) n)) a n)
    (hi : IntervalIntegrable
      (iteratedDerivWithin (2 * m) f (Icc (a : ℝ) n)) volume a n) :
    (∑ j ∈ Finset.Ico a n, f j) = (∫ x in (a : ℝ)..(n : ℝ), f x) +
      (f a - f n) / 2 + ∑ s ∈ Finset.Ico 1 m,
        ((bernoulli (2 * s) : ℝ) / (2 * s).factorial) *
          (iteratedDerivWithin (2 * s - 1) f (Icc (a : ℝ) n) n -
            iteratedDerivWithin (2 * s - 1) f (Icc (a : ℝ) n) a) +
              evenRemainder f m a n := by
  sorry

/-- The sharp periodic-Bernoulli supremum bounds the L¹ remainder.
Olver, Chapter 8, §2, pp. 284–287. -/
theorem abs_evenRemainder_le_integral {a n : ℤ} (han : a < n)
    {m : ℕ} (hm : 1 ≤ m) {f : ℝ → ℝ}
    (hi : IntervalIntegrable
      (iteratedDerivWithin (2 * m) f (Icc (a : ℝ) n)) volume a n) :
    |evenRemainder f m a n| ≤
      (2 - (2 : ℝ) ^ (1 - 2 * (m : ℝ))) * |(bernoulli (2 * m) : ℝ)| /
        (2 * m).factorial * ∫ x in (a : ℝ)..(n : ℝ),
          |iteratedDerivWithin (2 * m) f (Icc (a : ℝ) n) x| := by
  sorry

/-- A constant-sign highest derivative gives the remainder's sign and its
omitted-term bound. Olver, Chapter 8, §2, pp. 284–287. -/
theorem sign_and_abs_evenRemainder_le_endpoint {a n : ℤ} (han : a < n)
    {m : ℕ} (hm : 1 ≤ m) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (2 * m - 1) f (Icc (a : ℝ) n))
    (hac : AbsolutelyContinuousOnInterval
      (iteratedDerivWithin (2 * m - 1) f (Icc (a : ℝ) n)) a n)
    (hi : IntervalIntegrable
      (iteratedDerivWithin (2 * m) f (Icc (a : ℝ) n)) volume a n)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hsign : ∀ᵐ x ∂volume.restrict (Icc (a : ℝ) n),
      0 ≤ ε * iteratedDerivWithin (2 * m) f (Icc (a : ℝ) n) x) :
    0 ≤ (-1 : ℝ) ^ (m + 1) * ε * evenRemainder f m a n ∧
      |evenRemainder f m a n| ≤ (2 - (2 : ℝ) ^ (1 - 2 * (m : ℝ))) *
        |(bernoulli (2 * m) : ℝ) / (2 * m).factorial *
          (iteratedDerivWithin (2 * m - 1) f (Icc (a : ℝ) n) n -
            iteratedDerivWithin (2 * m - 1) f (Icc (a : ℝ) n) a)| := by
  sorry

/-- Two same-sign successive even derivatives improve the factor to one.
Olver, Chapter 8, §2, pp. 284–287. Absolute continuity is retained at the
highest antiderivative instead of assuming a continuous highest derivative. -/
theorem abs_evenRemainder_le_endpoint_of_two_even_signs {a n : ℤ} (han : a < n)
    {m : ℕ} (hm : 1 ≤ m) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (2 * m + 1) f (Icc (a : ℝ) n))
    (hac : AbsolutelyContinuousOnInterval
      (iteratedDerivWithin (2 * m + 1) f (Icc (a : ℝ) n)) a n)
    (hi : IntervalIntegrable
      (iteratedDerivWithin (2 * m + 2) f (Icc (a : ℝ) n)) volume a n)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hsign : ∀ x ∈ Icc (a : ℝ) n,
      0 ≤ ε * iteratedDerivWithin (2 * m) f (Icc (a : ℝ) n) x)
    (hsign' : ∀ᵐ x ∂volume.restrict (Icc (a : ℝ) n),
      0 ≤ ε * iteratedDerivWithin (2 * m + 2) f (Icc (a : ℝ) n) x) :
    |evenRemainder f m a n| ≤ |(bernoulli (2 * m) : ℝ) / (2 * m).factorial *
      (iteratedDerivWithin (2 * m - 1) f (Icc (a : ℝ) n) n -
        iteratedDerivWithin (2 * m - 1) f (Icc (a : ℝ) n) a)| := by
  sorry

/-- Absolute integrability of the final even derivative supplies the exact
constant in the improper Euler–Maclaurin expansion. Olver, Chapter 8, §2. -/
theorem tendsto_sum_sub_integral_sub_endpoint_terms {a : ℤ} {m : ℕ} (hm : 1 ≤ m)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ (2 * m - 1) f (Ici (a : ℝ)))
    (hac : ∀ n : ℤ, a < n → AbsolutelyContinuousOnInterval
      (iteratedDerivWithin (2 * m - 1) f (Ici (a : ℝ))) a n)
    (hi : IntegrableOn (iteratedDerivWithin (2 * m) f (Ici (a : ℝ))) (Ioi (a : ℝ))) :
    Tendsto (fun n : ℤ => (∑ j ∈ Finset.Ico a n, f j) -
      (∫ x in (a : ℝ)..(n : ℝ), f x) + f n / 2 -
        ∑ s ∈ Finset.Ico 1 m, ((bernoulli (2 * s) : ℝ) / (2 * s).factorial) *
          iteratedDerivWithin (2 * s - 1) f (Ici (a : ℝ)) n) atTop
      (𝓝 (f a / 2 - ∑ s ∈ Finset.Ico 1 m,
        ((bernoulli (2 * s) : ℝ) / (2 * s).factorial) *
          iteratedDerivWithin (2 * s - 1) f (Ici (a : ℝ)) a +
            ∫ x in Ioi (a : ℝ),
              ((bernoulli (2 * m) : ℝ) - periodicBernoulli (2 * m) x) /
                (2 * m).factorial * iteratedDerivWithin (2 * m) f (Ici (a : ℝ)) x)) := by
  sorry

end Real.EulerMaclaurin
