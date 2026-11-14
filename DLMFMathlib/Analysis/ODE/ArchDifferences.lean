/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Group.ForwardDiff

/-!
# Alternating differences of oscillation arches and zeros

Andrews, Askey and Roy, *Special Functions*, Theorem 4.15.1, pp. 229–230
(synopsis AAR-4.14.1–4.16.4). The highest derivative need only exist;
no extra continuity of that derivative is imposed.
-/

@[expose] public noncomputable section
open Set MeasureTheory
namespace ODE

/-- Lorch–Szegő arch and zero differences. Andrews–Askey–Roy, Theorem 4.15.1.
The sequences enumerate consecutive zeros inside an interval, without choosing an origin. -/
theorem arch_and_zero_forwardDifferences_pos {U : Set ℝ} (hU : IsOpen U)
    (hconvex : Convex ℝ U) {q y₁ y₂ y : ℝ → ℝ} {N : ℕ}
    (hq : ContinuousOn q U)
    (hsol : ∀ f ∈ [y₁, y₂, y], ∀ t ∈ U,
      HasDerivAt f (deriv f t) t ∧ HasDerivAt (deriv f) (-q t * f t) t)
    (hindep : ∃ t ∈ U, y₁ t * deriv y₂ t - deriv y₁ t * y₂ t ≠ 0)
    (hynonzero : ∃ t ∈ U, y t ≠ 0)
    (hdiff : ∀ n < N, DifferentiableOn ℝ
      (iteratedDeriv n (fun t => y₁ t ^ 2 + y₂ t ^ 2)) U)
    (hcont : ∀ n < N, ContinuousOn
      (iteratedDeriv n (fun t => y₁ t ^ 2 + y₂ t ^ 2)) U)
    (hpositive : ∀ n ≤ N, ∀ t ∈ U,
      0 < (-1 : ℝ) ^ n * iteratedDeriv n (fun t => y₁ t ^ 2 + y₂ t ^ 2) t)
    {x : ℕ → ℝ} (hx : StrictMono x) (hxU : ∀ k, x k ∈ U)
    (hzero : ∀ k, y (x k) = 0)
    (hnext : ∀ k, ∀ t ∈ Ioo (x k) (x (k + 1)), y t ≠ 0)
    {lam : ℝ} (hlam : -1 < lam) :
    (∀ k, IntervalIntegrable (fun t => |y t| ^ lam) volume (x k) (x (k + 1))) ∧
    (∀ n ≤ N, ∀ k, 0 < (-1 : ℝ) ^ n *
      (fwdDiff (1 : ℕ))^[n]
        (fun j => ∫ t in x j..x (j + 1), |y t| ^ lam) k) ∧
    ∀ n, 1 ≤ n → n ≤ N + 1 → ∀ k,
      0 < (-1 : ℝ) ^ (n - 1) * (fwdDiff (1 : ℕ))^[n] x k := by
  sorry

/-- Alternating differences of corresponding zeros of two solutions.
Andrews–Askey–Roy, Theorem 4.15.1, final assertion. A fixed shift of either
zero sequence is permitted; only their initial ordering is required. -/
theorem zero_offset_forwardDifferences_pos {U : Set ℝ} (hU : IsOpen U)
    (hconvex : Convex ℝ U) {q y₁ y₂ y v : ℝ → ℝ} {N : ℕ}
    (hq : ContinuousOn q U)
    (hsol : ∀ f ∈ [y₁, y₂, y, v], ∀ t ∈ U,
      HasDerivAt f (deriv f t) t ∧ HasDerivAt (deriv f) (-q t * f t) t)
    (hindep : ∃ t ∈ U, y₁ t * deriv y₂ t - deriv y₁ t * y₂ t ≠ 0)
    (hynonzero : ∃ t ∈ U, y t ≠ 0) (hvnonzero : ∃ t ∈ U, v t ≠ 0)
    (hdiff : ∀ n < N, DifferentiableOn ℝ
      (iteratedDeriv n (fun t => y₁ t ^ 2 + y₂ t ^ 2)) U)
    (hcont : ∀ n < N, ContinuousOn
      (iteratedDeriv n (fun t => y₁ t ^ 2 + y₂ t ^ 2)) U)
    (hpositive : ∀ n ≤ N, ∀ t ∈ U,
      0 < (-1 : ℝ) ^ n * iteratedDeriv n (fun t => y₁ t ^ 2 + y₂ t ^ 2) t)
    {x z : ℕ → ℝ} (hx : StrictMono x) (hz : StrictMono z)
    (hxU : ∀ k, x k ∈ U) (hzU : ∀ k, z k ∈ U)
    (hzero : ∀ k, y (x k) = 0 ∧ v (z k) = 0)
    (hnext : ∀ k, (∀ t ∈ Ioo (x k) (x (k + 1)), y t ≠ 0) ∧
      ∀ t ∈ Ioo (z k) (z (k + 1)), v t ≠ 0)
    (horder : x 0 < z 0) :
    ∀ n ≤ N, ∀ k, 0 < (-1 : ℝ) ^ n *
      (fwdDiff (1 : ℕ))^[n] (fun j => z j - x j) k := by
  sorry

/-- The finite-window Lorch–Szegő theorem on a possibly closed interval.
Andrews–Askey–Roy, Theorem 4.15.1. Only `n+2` consecutive zeros are required;
the highest amplitude derivative exists only in the interior. -/
theorem finite_arch_and_zero_forwardDifferences_pos {U : Set ℝ}
    (hconvex : Convex ℝ U) {q y₁ y₂ y : ℝ → ℝ} (n : ℕ)
    (hq : ContinuousOn q U)
    (hsol : ∀ f ∈ [y₁, y₂, y], ∀ t ∈ U,
      HasDerivAt f (deriv f t) t ∧ HasDerivAt (deriv f) (-q t * f t) t)
    (hindep : ∃ t ∈ U, y₁ t * deriv y₂ t - deriv y₁ t * y₂ t ≠ 0)
    (hynonzero : ∃ t ∈ U, y t ≠ 0)
    (hdiff : ∀ j < n, DifferentiableOn ℝ
      (iteratedDeriv j (fun t => y₁ t ^ 2 + y₂ t ^ 2)) (interior U))
    (hcont : ∀ j < n, ContinuousOn
      (iteratedDeriv j (fun t => y₁ t ^ 2 + y₂ t ^ 2)) U)
    (hpositive : ∀ j ≤ n, ∀ t ∈ interior U,
      0 < (-1 : ℝ) ^ j * iteratedDeriv j (fun t => y₁ t ^ 2 + y₂ t ^ 2) t)
    {x : ℕ → ℝ} (hx : StrictMonoOn x (Iic (n + 1)))
    (hxU : ∀ k ≤ n + 1, x k ∈ U) (hzero : ∀ k ≤ n + 1, y (x k) = 0)
    (hnext : ∀ k ≤ n, ∀ t ∈ Ioo (x k) (x (k + 1)), y t ≠ 0)
    {lam : ℝ} (hlam : -1 < lam) :
    (∀ k ≤ n, IntervalIntegrable (fun t => |y t| ^ lam) volume (x k) (x (k + 1))) ∧
    0 < (-1 : ℝ) ^ n * (fwdDiff (1 : ℕ))^[n]
      (fun j => ∫ t in x j..x (j + 1), |y t| ^ lam) 0 ∧
    0 < (-1 : ℝ) ^ n * (fwdDiff (1 : ℕ))^[n + 1] x 0 := by
  sorry

/-- The finite-window alternating difference of corresponding solution zeros.
Andrews–Askey–Roy, Theorem 4.15.1, final assertion. Only `n+1` paired zeros
are used, so the result applies on finite closed regular intervals. -/
theorem finite_zero_offset_forwardDifferences_pos {U : Set ℝ}
    (hconvex : Convex ℝ U) {q y₁ y₂ y v : ℝ → ℝ} (n : ℕ)
    (hq : ContinuousOn q U)
    (hsol : ∀ f ∈ [y₁, y₂, y, v], ∀ t ∈ U,
      HasDerivAt f (deriv f t) t ∧ HasDerivAt (deriv f) (-q t * f t) t)
    (hindep : ∃ t ∈ U, y₁ t * deriv y₂ t - deriv y₁ t * y₂ t ≠ 0)
    (hynonzero : ∃ t ∈ U, y t ≠ 0) (hvnonzero : ∃ t ∈ U, v t ≠ 0)
    (hdiff : ∀ j < n, DifferentiableOn ℝ
      (iteratedDeriv j (fun t => y₁ t ^ 2 + y₂ t ^ 2)) (interior U))
    (hcont : ∀ j < n, ContinuousOn
      (iteratedDeriv j (fun t => y₁ t ^ 2 + y₂ t ^ 2)) U)
    (hpositive : ∀ j ≤ n, ∀ t ∈ interior U,
      0 < (-1 : ℝ) ^ j * iteratedDeriv j (fun t => y₁ t ^ 2 + y₂ t ^ 2) t)
    {x z : ℕ → ℝ} (hx : StrictMonoOn x (Iic n)) (hz : StrictMonoOn z (Iic n))
    (hxU : ∀ k ≤ n, x k ∈ U) (hzU : ∀ k ≤ n, z k ∈ U)
    (hzero : ∀ k ≤ n, y (x k) = 0 ∧ v (z k) = 0)
    (hnext : ∀ k < n, (∀ t ∈ Ioo (x k) (x (k + 1)), y t ≠ 0) ∧
      ∀ t ∈ Ioo (z k) (z (k + 1)), v t ≠ 0)
    (horder : x 0 < z 0) :
    0 < (-1 : ℝ) ^ n * (fwdDiff (1 : ℕ))^[n] (fun j => z j - x j) 0 := by
  sorry

/-- Sturm's strict comparison before the first zero for matching nonzero initial data.
Andrews–Askey–Roy, Theorem 4.14.2 (synopsis AAR-4.14.1–4.16.4).
A zero at the initial endpoint is permitted, but is not counted as the first later zero. -/
theorem abs_solution_lt_of_potential_lt {a b : ℝ} (hab : a < b)
    {q₁ q₂ u₁ u₂ : ℝ → ℝ} (hq₁ : ContinuousOn q₁ (Ioo a b))
    (hq₂ : ContinuousOn q₂ (Ioo a b))
    (hcontinuous₁ : ContinuousOn u₁ (Icc a b) ∧ ContinuousOn (deriv u₁) (Icc a b))
    (hcontinuous₂ : ContinuousOn u₂ (Icc a b) ∧ ContinuousOn (deriv u₂) (Icc a b))
    (hsol₁ : ∀ t ∈ Ioo a b,
      HasDerivAt u₁ (deriv u₁ t) t ∧ HasDerivAt (deriv u₁) (-q₁ t * u₁ t) t)
    (hsol₂ : ∀ t ∈ Ioo a b,
      HasDerivAt u₂ (deriv u₂ t) t ∧ HasDerivAt (deriv u₂) (-q₂ t * u₂ t) t)
    (hpotential : ∀ t ∈ Ioo a b, q₂ t < q₁ t)
    (hinit : u₁ a = u₂ a ∧ deriv u₁ a = deriv u₂ a)
    (hnonzero : u₁ a ≠ 0 ∨ deriv u₁ a ≠ 0)
    (hnext : ∀ t ∈ Ioo a b, u₁ t ≠ 0) :
    (∀ t ∈ Ioo a b, |u₁ t| < |u₂ t|) ∧
      (u₁ b = 0 → u₂ b ≠ 0) := by
  sorry

end ODE
