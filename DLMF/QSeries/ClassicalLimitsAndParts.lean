/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Jackson integration by parts and classical q limits

Andrews, Askey and Roy, *Special Functions*, §§10.1–10.2. Endpoint-series
summability is explicit in integration by parts; no Jackson derivative at zero
is required. Infinite-product quotients retain the principal complex power.
-/

@[expose] public section

open Filter
open scoped Topology Classical

noncomputable section

namespace DLMF.QSeries

/-- Jackson integration by parts between nonnegative real endpoints.
Andrews–Askey–Roy, *Special Functions*, §10.1
(synopsis AAR-10.1–10.2.4). -/
theorem jacksonIntegral_integration_by_parts {q a b : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (ha : 0 ≤ a) (hab : a < b)
    (f g : ℂ → ℂ) (hf : ContinuousAt (fun x : ℝ => f x) 0)
    (hg : ContinuousAt (fun x : ℝ => g x) 0)
    (hsum : ∀ c ∈ ({a, b} : Finset ℝ), 0 < c →
      Summable (fun j : ℕ => q ^ j *
        (‖f (c * q ^ j) * qDeriv q g (c * q ^ j)‖ +
          ‖g (c * q ^ (j + 1)) * qDeriv q f (c * q ^ j)‖))) :
    jacksonIntegral q b (fun x => f x * qDeriv q g x) -
        jacksonIntegral q a (fun x => f x * qDeriv q g x) =
      f b * g b - f a * g a -
        (jacksonIntegral q b (fun x => g (q * x) * qDeriv q f x) -
          jacksonIntegral q a (fun x => g (q * x) * qDeriv q f x)) := by
  sorry

/-- Jackson integrals of continuous functions tend to ordinary integrals as q tends to one.
Andrews–Askey–Roy, *Special Functions*, §10.1
(synopsis AAR-10.1–10.2.4). -/
theorem tendsto_jacksonIntegral_one {a : ℝ} (ha : 0 ≤ a) (f : ℂ → ℂ)
    (hf : ContinuousOn (fun x : ℝ => f x) (Set.Icc 0 a)) :
    Tendsto (fun q : ℝ => jacksonIntegral q a f) (𝓝[<] 1)
      (𝓝 (∫ x : ℝ in (0 : ℝ)..a, f x)) := by
  sorry

/-- Uniform q-binomial product-ratio convergence on the closed unit disk.
Andrews–Askey–Roy, *Special Functions*, Theorem 10.2.4
(synopsis AAR-10.1–10.2.4). -/
theorem tendstoUniformlyOn_qPochhammerInf_ratio {lam mu : ℝ}
    (horder : lam ≤ mu) (hsum : 1 ≤ mu + lam) :
    TendstoUniformlyOn (fun q : ℝ => fun z : ℂ =>
      qPochhammerInf (((q ^ lam : ℝ) : ℂ) * z) q /
        qPochhammerInf (((q ^ mu : ℝ) : ℂ) * z) q)
      (fun z : ℂ => (1 - z) ^ ((mu - lam : ℝ) : ℂ)) (𝓝[<] 1)
      (Metric.closedBall 0 1) := by
  sorry

/-- For arbitrary real exponents the product-ratio limit is locally uniform away from one.
Andrews–Askey–Roy, *Special Functions*, Theorem 10.2.4
(synopsis AAR-10.1–10.2.4). -/
theorem tendstoLocallyUniformlyOn_qPochhammerInf_ratio (lam mu : ℝ) :
    TendstoLocallyUniformlyOn (fun q : ℝ => fun z : ℂ =>
      qPochhammerInf (((q ^ lam : ℝ) : ℂ) * z) q /
        qPochhammerInf (((q ^ mu : ℝ) : ℂ) * z) q)
      (fun z : ℂ => (1 - z) ^ ((mu - lam : ℝ) : ℂ)) (𝓝[<] 1)
      {z | ‖z‖ ≤ 1 ∧ z ≠ 1} := by
  sorry

end DLMF.QSeries
