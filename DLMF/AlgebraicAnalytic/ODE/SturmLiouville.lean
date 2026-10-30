/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.ODE.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Sturm–Liouville systems and the Liouville normal form (DLMF §1.13(viii))

For the Sturm–Liouville equation 1.13.26 `(p u')' + (λρ - q) u = 0` on `[a, b]` with unmixed
(1.13.27) or periodic (1.13.28) boundary conditions:

* the eigenvalues of a regular system form a sequence tending to `+∞` (admitted);
* the Liouville transformation 1.13.30 `t = ∫_a^x √(ρ/p)`, `w(t) = u(x) (pρ)^{1/4}` to the
  normal form 1.13.29 `ẅ + (λ - q̂(t)) w = 0` with `q̂` as in 1.13.31 (admitted);
* the correspondence of eigenvalues (admitted) and of nodes (proved) under the transformation.

The transformation is stated with `m = (pρ)^{1/4}`, `T(x) = ∫_a^x √(ρ/p)` and its inverse `X`
given by hypotheses, so that no new definitions are needed.

DLMF §1.13(viii) also says that periodic boundary conditions are carried to periodic ones. This
holds only when `pρ`, its derivative and `ρ/p` agree at `a` and `b` (for example for
`(b - a)`-periodic coefficients), since `w(0) = m(a) u(a)` and `w(c) = m(b) u(b)`; the periodic
statement below carries these hypotheses.
-/

@[expose] public noncomputable section

open Set

namespace DLMF.AlgebraicAnalytic

/-- DLMF §1.13(viii): a regular Sturm–Liouville system 1.13.26–1.13.27 on `[a, b]`, with `p` of
class `C¹`, `q`, `ρ` continuous and `p, ρ > 0` on `[a, b]`, has infinitely many eigenvalues;
they are bounded below and only finitely many lie below any given bound, so they form a
sequence `λ₀ < λ₁ < ⋯ → ∞`. -/
@[dlmf 1.13.viii]
theorem regularSL_eigenvalues {p q ρ : ℝ → ℝ} {a b α α' β β' : ℝ} (hab : a < b)
    (hp : ContDiffOn ℝ 1 p (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ x ∈ Icc a b, 0 < p x ∧ 0 < ρ x)
    (hα : α ≠ 0 ∨ α' ≠ 0) (hβ : β ≠ 0 ∨ β' ≠ 0) :
    {lam | IsRegularSLEigenvalue p q ρ a b α α' β β' lam}.Infinite ∧
      BddBelow {lam | IsRegularSLEigenvalue p q ρ a b α α' β β' lam} ∧
      ∀ c, ({lam | IsRegularSLEigenvalue p q ρ a b α α' β β' lam} ∩ Iio c).Finite := by
  sorry

/-- DLMF 1.13.29–1.13.31 (Liouville normal form): let `p, ρ > 0` be of class `C²` and `q`
continuous on `(a, b)`, let `T` be a primitive of `√(ρ/p)` on `(a, b)` with `X` its inverse
(`T(X t) = t`, `X t ∈ (a, b)` for `t ∈ T '' (a, b)`), and `m = (pρ)^{1/4}`. If `u` solves
1.13.26 on `(a, b)`, then `w(t) = u(X t) m(X t)` solves `ẅ + (λ - q̂(t)) w = 0` (1.13.29) on
`T '' (a, b)`, where `q̂ = q/ρ + m⁻¹ d²m/dt²` (1.13.31) with `m` as a function of `t`. -/
@[dlmf 1.13.E29, dlmf 1.13.E30, dlmf 1.13.E31]
theorem liouville_normal_form {p q ρ T X u : ℝ → ℝ} {a b lam : ℝ}
    (hp : ContDiffOn ℝ 2 p (Ioo a b)) (hρ : ContDiffOn ℝ 2 ρ (Ioo a b))
    (hq : ContinuousOn q (Ioo a b)) (hpos : ∀ x ∈ Ioo a b, 0 < p x ∧ 0 < ρ x)
    (hT : ∀ x ∈ Ioo a b, HasDerivAt T (Real.sqrt (ρ x / p x)) x)
    (hX : ∀ t ∈ T '' Ioo a b, X t ∈ Ioo a b ∧ T (X t) = t)
    (hu : IsSturmLiouvilleSolOn p q ρ lam u (Ioo a b)) :
    ∀ t ∈ T '' Ioo a b,
      let m : ℝ → ℝ := fun t => (p (X t) * ρ (X t)) ^ (1 / 4 : ℝ)
      let w : ℝ → ℝ := fun t => u (X t) * m t
      DifferentiableAt ℝ w t ∧
        HasDerivAt (deriv w)
          (-(lam - (q (X t) / ρ (X t) + (m t)⁻¹ * iteratedDeriv 2 m t)) * w t) t := by
  sorry

/-- DLMF §1.13(viii), the nodes: if `T` maps `(a, b)` bijectively onto `(0, c)` and
`w(T x) = u(x) m(x)` with `m > 0`, then `u` on `(a, b)` and `w` on `(0, c)` have the same
number of zeros (possibly infinite). -/
@[dlmf 1.13.viii]
theorem liouville_nodes {T u w m : ℝ → ℝ} {a b c : ℝ} (hT : BijOn T (Ioo a b) (Ioo 0 c))
    (hm : ∀ x ∈ Ioo a b, 0 < m x) (hw : ∀ x ∈ Ioo a b, w (T x) = u x * m x) :
    {t ∈ Ioo 0 c | w t = 0}.encard = {x ∈ Ioo a b | u x = 0}.encard := by
  have himage : {t ∈ Ioo 0 c | w t = 0} = T '' {x ∈ Ioo a b | u x = 0} := by
    ext t
    constructor
    · rintro ⟨ht, hwt⟩
      obtain ⟨x, hx, rfl⟩ := hT.surjOn ht
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      rw [hw x hx] at hwt
      exact (mul_eq_zero.mp hwt).resolve_right (hm x hx).ne'
    · rintro ⟨x, ⟨hx, hux⟩, rfl⟩
      exact ⟨hT.mapsTo hx, by rw [hw x hx, hux, zero_mul]⟩
  rw [himage, (hT.injOn.mono (sep_subset _ _)).encard_image]

/-- DLMF §1.13(viii), eigenvalues and unmixed boundary conditions: under the Liouville
transformation (with `p, ρ` of class `C²`, `q` continuous, `p, ρ > 0` on `[a, b]`,
`T(x) = ∫_a^x √(ρ/p)`, `c = T(b)`, `m = (pρ)^{1/4}`, and `q̂` as in 1.13.31), the regular system
1.13.26–1.13.27 and the normal form 1.13.29 on `[0, c]` with the unmixed boundary conditions
`γ w(0) + γ' w'(0) = 0`, `δ w(c) + δ' w'(c) = 0`, where
`γ = α/m(a) - α' m'(a)/m(a)²`, `γ' = α' √(ρ(a)/p(a))/m(a)` and similarly at `b`, have the same
eigenvalues. The coefficients are taken `C²` and positive on all of `ℝ` (any `C²` positive
data on `[a, b]` extend so), so that the two-sided derivatives at `a`, `b` used by
`IsRegularSLEigenvalue` and `X = T⁻¹` near `0` and `c` are meaningful. -/
@[dlmf 1.13.viii]
theorem liouville_eigenvalues_unmixed {p q ρ T X qhat : ℝ → ℝ} {a b α α' β β' : ℝ}
    (hab : a < b) (hp : ContDiff ℝ 2 p) (hρ : ContDiff ℝ 2 ρ)
    (hq : ContinuousOn q (Icc a b)) (hpos : ∀ x, 0 < p x ∧ 0 < ρ x)
    (hα : α ≠ 0 ∨ α' ≠ 0) (hβ : β ≠ 0 ∨ β' ≠ 0)
    (hT : ∀ x, T x = ∫ s in a..x, Real.sqrt (ρ s / p s))
    (hX : ∀ x, X (T x) = x)
    (hqhat : ∀ t ∈ Icc 0 (T b), qhat t = q (X t) / ρ (X t) +
      ((p (X t) * ρ (X t)) ^ (1 / 4 : ℝ))⁻¹ *
        iteratedDeriv 2 (fun s => (p (X s) * ρ (X s)) ^ (1 / 4 : ℝ)) t) (lam : ℝ) :
    let m : ℝ → ℝ := fun x => (p x * ρ x) ^ (1 / 4 : ℝ)
    IsRegularSLEigenvalue p q ρ a b α α' β β' lam ↔
      IsRegularSLEigenvalue (fun _ => 1) qhat (fun _ => 1) 0 (T b)
        (α / m a - α' * deriv m a / m a ^ 2) (α' * Real.sqrt (ρ a / p a) / m a)
        (β / m b - β' * deriv m b / m b ^ 2) (β' * Real.sqrt (ρ b / p b) / m b) lam := by
  sorry

/-- DLMF §1.13(viii), eigenvalues and periodic boundary conditions: as in
`liouville_eigenvalues_unmixed`, the periodic system 1.13.26, 1.13.28 and the periodic normal
form on `[0, c]` have the same eigenvalues, provided `m = (pρ)^{1/4}`, `m'` and `ρ/p` take the
same values at `a` and `b` (needed for periodicity to be preserved; see the module docstring). -/
@[dlmf 1.13.viii]
theorem liouville_eigenvalues_periodic {p q ρ T X qhat : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hp : ContDiff ℝ 2 p) (hρ : ContDiff ℝ 2 ρ)
    (hq : ContinuousOn q (Icc a b)) (hpos : ∀ x, 0 < p x ∧ 0 < ρ x)
    (hT : ∀ x, T x = ∫ s in a..x, Real.sqrt (ρ s / p s))
    (hX : ∀ x, X (T x) = x)
    (hqhat : ∀ t ∈ Icc 0 (T b), qhat t = q (X t) / ρ (X t) +
      ((p (X t) * ρ (X t)) ^ (1 / 4 : ℝ))⁻¹ *
        iteratedDeriv 2 (fun s => (p (X s) * ρ (X s)) ^ (1 / 4 : ℝ)) t)
    (hma : (p a * ρ a) ^ (1 / 4 : ℝ) = (p b * ρ b) ^ (1 / 4 : ℝ))
    (hma' : deriv (fun x => (p x * ρ x) ^ (1 / 4 : ℝ)) a =
      deriv (fun x => (p x * ρ x) ^ (1 / 4 : ℝ)) b)
    (hra : ρ a / p a = ρ b / p b) (lam : ℝ) :
    IsPeriodicSLEigenvalue p q ρ a b lam ↔
      IsPeriodicSLEigenvalue (fun _ => 1) qhat (fun _ => 1) 0 (T b) lam := by
  sorry

end DLMF.AlgebraicAnalytic
