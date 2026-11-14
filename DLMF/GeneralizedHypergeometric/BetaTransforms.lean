/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.Gamma.BetaFunction
public import DLMF.Hypergeometric.Basic

/-!
# Beta transforms of finite hypergeometric expressions

Rao–Lakshminarayanan, *Generalized Hypergeometric Functions* (2018), Chapter 8,
(8.7)–(8.14). The coefficient formula evaluates each finite transformed expression
explicitly, including polynomial prefactors and powers of `1-t`.
-/

@[expose] public noncomputable section
open Complex MeasureTheory Finset
open scoped Nat
namespace DLMF.Hypergeometric.BetaTransform

/-- The normalized beta transform, Rao–Lakshminarayanan (8.11)–(8.13),
synopsis RL-8.06. Its analytic domain is `0 < Re d < Re e` and the weighted
integrand must be integrable; the formula itself uses the totalized integral. -/
def value (d e : ℂ) (f : ℝ → ℂ) : ℂ :=
  Gamma e / (Gamma d * Gamma (e - d)) *
    ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (d - 1) * (1 - t : ℂ) ^ (e - d - 1) * f t

/-- The defining normalized integral of RL-8.06. -/
theorem value_def (d e : ℂ) (f : ℝ → ℂ) :
    value d e f = Gamma e / (Gamma d * Gamma (e - d)) *
      ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (d - 1) * (1 - t : ℂ) ^ (e - d - 1) * f t := rfl

/-- Beta moments of two monomials, Rao–Lakshminarayanan (8.11)–(8.13), RL-8.06. -/
theorem value_monomial_mul_one_sub {d e : ℂ} (hd : 0 < d.re)
    (hed : 0 < (e - d).re) (k l : ℕ) :
    value d e (fun t => (t : ℂ) ^ k * (1 - t : ℂ) ^ l) =
      pochhammer d k * pochhammer (e - d) l / pochhammer e (k + l) := by
  sorry

/-- Finite polynomial evaluation under the beta transform,
Rao–Lakshminarayanan (8.11)–(8.13), synopsis RL-8.06. -/
theorem value_polynomial {d e : ℂ} (hd : 0 < d.re) (hed : 0 < (e - d).re)
    (P : Polynomial ℂ) :
    value d e (fun t => P.eval (t : ℂ)) =
      ∑ k ∈ P.support, P.coeff k * pochhammer d k / pochhammer e k := by
  sorry

/-- Master coefficient evaluation for every finite transformed expression,
Rao–Lakshminarayanan §§8.4–8.5, synopsis RL-8.07. The endpoint inequality
is imposed separately for every retained term. -/
theorem value_finite_hypergeometric (A B : Multiset ℂ) (P : Polynomial ℂ)
    (N r s : ℕ) (κ lam d e : ℂ)
    (hd : 0 < d.re) (hed : 0 < (e - d).re)
    (hint : ∀ k ≤ N, 0 < (e - d + lam - s * k).re)
    (hreg : ∀ k ≤ N, pochhammerProduct B k ≠ 0) :
    value d e (fun t => P.eval (t : ℂ) * (1 - t : ℂ) ^ lam *
      generalizedHypergeometricTruncated N A B
        (κ * (t : ℂ) ^ r / (1 - t : ℂ) ^ s)) =
      ∑ j ∈ P.support, ∑ k ∈ range (N + 1),
        P.coeff j * κ ^ k * generalizedHypergeometricCoeff A B k *
          (Gamma e * Gamma (d + r * k + j) * Gamma (e - d + lam - s * k) /
            (Gamma d * Gamma (e - d) * Gamma (e + lam + ((r : ℂ) - s) * k + j))) := by
  sorry

/-- Erdélyi's first product integral, Rao–Lakshminarayanan (8.7), synopsis RL-8.03.
All variable powers use the principal branch near the origin. -/
theorem erdelyi_first (a b c m l : ℂ) {z : ℂ} (hz : ‖z‖ < 1 / 2)
    (hm : 0 < m.re) (hcm : 0 < (c - m).re)
    (hreg : LowerParametersRegular {c, m, c - m}) :
    ordinaryHypergeometric a b c z = value m c (fun t =>
      (1 - z * t) ^ (l - a - b) *
        ordinaryHypergeometric (l - a) (l - b) m (z * t) *
        ordinaryHypergeometric (a + b - l) (l - m) (c - m)
          (z * (1 - t) / (1 - z * t))) := by
  sorry

/-- Erdélyi's second product integral, Rao–Lakshminarayanan (8.8), synopsis RL-8.04. -/
theorem erdelyi_second (a b c m a' : ℂ) {z : ℂ} (hz : ‖z‖ < 1 / 2)
    (hm : 0 < m.re) (hcm : 0 < (c - m).re)
    (hreg : LowerParametersRegular {c, m, c - m}) :
    ordinaryHypergeometric a b c z = value m c (fun t =>
      (1 - z * t) ^ (-a') * ordinaryHypergeometric (a - a') b m (z * t) *
        ordinaryHypergeometric a' (b - m) (c - m) (z * (1 - t) / (1 - z * t))) := by
  sorry

/-- Erdélyi's `₃F₂` integral, Rao–Lakshminarayanan (8.9), synopsis RL-8.05,
with the spurious factor involving an unbound parameter omitted as in the synopsis. -/
theorem erdelyi_threeF2 (a b c m l n : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    (hm : 0 < m.re) (hl : 0 < l.re) (hn : 0 < n.re)
    (hex : 0 < (c + m - l - n).re)
    (hreg : LowerParametersRegular {c, l, n, c + m - l - n}) :
    ordinaryHypergeometric a b c z =
      Gamma c * Gamma m / (Gamma l * Gamma n * Gamma (c + m - l - n)) *
        ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (m - 1) *
          (1 - t : ℂ) ^ (c + m - l - n - 1) *
          ordinaryHypergeometric (m - l) (c - l) (c + m - l - n) (1 - (t : ℂ)) *
          generalizedHypergeometric {a, b, m} {l, n} (z * t) := by
  sorry

end DLMF.Hypergeometric.BetaTransform
