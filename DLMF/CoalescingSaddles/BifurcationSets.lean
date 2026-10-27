/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.CoalescingSaddles.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Bifurcation sets (DLMF §36.4)

Statements acquired from the NIST DLMF (version 1.2.8), checked 2026-10-26.

The critical points (36.4.1, 36.4.2) and bifurcation sets (36.4.3, 36.4.4) are defined in
`DLMF.CoalescingSaddles.Basic` with complex derivatives of the polynomial potentials. Here the
explicit descriptions 36.4.5–36.4.13 are proved: the fold, cusp and swallowtail bifurcation sets,
the swallowtail self-intersection line and ribs, the elliptic umbilic astroid and ribs, and the
hyperbolic umbilic bifurcation set and rib. Two statements are adjusted: the self-intersection line
36.4.8 has `z < 0` (DLMF: `z ≤ 0`; the origin is only a limit point), and the hyperbolic umbilic
parametrization 36.4.12 is stated for `z ≠ 0` (the slice `z = 0` consists of two half-lines that
the parametrization does not produce). The cusp lines are formalized as `cuspoidCuspLines` and
`umbilicCuspLines` (Basic). The bounds `j_max ≤ K + 1` and `j_max ≤ 4` on the
number of real critical points are proved by mapping the critical points injectively into the
roots of a nonzero complex polynomial (`q2s_finite_ncard_le_of_poly`).

The derivatives are computed through `s36a_hasDerivAt_poly`: the derivative of
`∑_{i ≤ N} cᵢ uⁱ` is `∑_{i < N} (i+1) c_{i+1} uⁱ`.
-/

@[expose] public noncomputable section

open Complex Set Finset Polynomial
open scoped Real

namespace DLMF.CoalescingSaddles

/-! ### Derivatives of polynomials -/

lemma s36a_hasDerivAt_poly (c : ℕ → ℂ) (N : ℕ) (t : ℂ) :
    HasDerivAt (fun u => ∑ i ∈ range (N + 1), c i * u ^ i)
      (∑ i ∈ range N, ((i : ℂ) + 1) * c (i + 1) * t ^ i) t := by
  have h := HasDerivAt.sum (u := range (N + 1)) (A := fun i u => c i * u ^ i)
    (fun i _ => (hasDerivAt_pow i t).const_mul (c i))
  convert h using 1
  · funext u; simp
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.cast_add, Nat.cast_one,
      Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

lemma s36a_deriv_poly (c : ℕ → ℂ) (N : ℕ) :
    deriv (fun u => ∑ i ∈ range (N + 1), c i * u ^ i) =
      fun t => ∑ i ∈ range N, (((i : ℂ) + 1) * c (i + 1)) * t ^ i := by
  funext t; exact (s36a_hasDerivAt_poly c N t).deriv

lemma s36a_iteratedDeriv_two (f : ℂ → ℂ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

lemma s36a_iteratedDeriv_three (f : ℂ → ℂ) : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [iteratedDeriv_succ, s36a_iteratedDeriv_two]

/-! ### Cuspoid potentials of low codimension -/

lemma s36a_fold_derivs (x : Fin 1 → ℝ) (t : ℂ) :
    deriv (fun u => cuspoidPotential 1 u x) t = 3 * t ^ 2 + x 0 ∧
      iteratedDeriv 2 (fun u => cuspoidPotential 1 u x) t = 6 * t := by
  have hf : (fun u => cuspoidPotential 1 u x) = fun u => ∑ i ∈ range (3 + 1),
      (fun i : ℕ => if i = 1 then (x 0 : ℂ) else if i = 3 then 1 else 0) i * u ^ i := by
    funext u; simp [cuspoidPotential, Finset.sum_range_succ]; ring
  rw [s36a_iteratedDeriv_two, hf, s36a_deriv_poly, s36a_deriv_poly]
  constructor
  · simp [Finset.sum_range_succ]; ring
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]; norm_num

theorem s36a_cusp_derivs (x : Fin 2 → ℝ) (t : ℂ) :
    deriv (fun u => cuspoidPotential 2 u x) t = 4 * t ^ 3 + 2 * x 1 * t + x 0 ∧
      iteratedDeriv 2 (fun u => cuspoidPotential 2 u x) t = 12 * t ^ 2 + 2 * x 1 := by
  have hf : (fun u => cuspoidPotential 2 u x) = fun u => ∑ i ∈ range (4 + 1),
      (fun i : ℕ => if i = 1 then (x 0 : ℂ) else if i = 2 then (x 1 : ℂ) else
        if i = 4 then 1 else 0) i * u ^ i := by
    funext u; simp [cuspoidPotential, Finset.sum_range_succ, Fin.sum_univ_two]; ring
  rw [s36a_iteratedDeriv_two, hf, s36a_deriv_poly, s36a_deriv_poly]
  constructor <;> simp [Finset.sum_range_succ] <;> ring

lemma s36a_swallowtail_derivs (x : Fin 3 → ℝ) (t : ℂ) :
    deriv (fun u => cuspoidPotential 3 u x) t = 5 * t ^ 4 + 3 * x 2 * t ^ 2 + 2 * x 1 * t + x 0 ∧
      iteratedDeriv 2 (fun u => cuspoidPotential 3 u x) t = 20 * t ^ 3 + 6 * x 2 * t + 2 * x 1 ∧
      iteratedDeriv 3 (fun u => cuspoidPotential 3 u x) t = 60 * t ^ 2 + 6 * x 2 := by
  have hf : (fun u => cuspoidPotential 3 u x) = fun u => ∑ i ∈ range (5 + 1),
      (fun i : ℕ => if i = 1 then (x 0 : ℂ) else if i = 2 then (x 1 : ℂ) else
        if i = 3 then (x 2 : ℂ) else if i = 5 then 1 else 0) i * u ^ i := by
    funext u; simp [cuspoidPotential, Finset.sum_range_succ, Fin.sum_univ_three]; ring
  rw [s36a_iteratedDeriv_two, s36a_iteratedDeriv_three, hf, s36a_deriv_poly, s36a_deriv_poly,
    s36a_deriv_poly]
  refine ⟨?_, ?_, ?_⟩ <;> simp [Finset.sum_range_succ] <;> ring

/-! ### Derivatives of the umbilic potentials -/

lemma s36a_deriv_cubic (a b c d : ℂ) :
    deriv (fun u : ℂ => a * u ^ 3 + b * u ^ 2 + c * u + d) =
      fun u => 3 * a * u ^ 2 + 2 * b * u + c := by
  have hf : (fun u : ℂ => a * u ^ 3 + b * u ^ 2 + c * u + d) = fun u => ∑ i ∈ range (3 + 1),
      (fun i : ℕ => if i = 0 then d else if i = 1 then c else if i = 2 then b else a) i *
        u ^ i := by
    funext u; simp [Finset.sum_range_succ]; ring
  rw [hf, s36a_deriv_poly]
  funext u; simp [Finset.sum_range_succ]; ring

lemma s36a_E_ds (t : ℂ) (x y z : ℝ) :
    deriv (fun u => ellipticUmbilicPotential u t x y z) =
      fun u => 3 * u ^ 2 - 3 * t ^ 2 + 2 * z * u + x := by
  rw [show (fun u => ellipticUmbilicPotential u t x y z) = fun u : ℂ =>
      1 * u ^ 3 + (z : ℂ) * u ^ 2 + (-3 * t ^ 2 + x) * u + (z * t ^ 2 + y * t) from
        funext fun u => by simp only [ellipticUmbilicPotential]; ring, s36a_deriv_cubic]
  funext u; ring

lemma s36a_E_dt (s : ℂ) (x y z : ℝ) :
    deriv (fun u => ellipticUmbilicPotential s u x y z) =
      fun u => -6 * s * u + 2 * z * u + y := by
  rw [show (fun u => ellipticUmbilicPotential s u x y z) = fun u : ℂ =>
      0 * u ^ 3 + (z - 3 * s) * u ^ 2 + (y : ℂ) * u + (s ^ 3 + z * s ^ 2 + x * s) from
        funext fun u => by simp only [ellipticUmbilicPotential]; ring, s36a_deriv_cubic]
  funext u; ring

lemma s36a_H_ds (t : ℂ) (x y z : ℝ) :
    deriv (fun u => hyperbolicUmbilicPotential u t x y z) =
      fun u => 3 * u ^ 2 + z * t + x := by
  rw [show (fun u => hyperbolicUmbilicPotential u t x y z) = fun u : ℂ =>
      1 * u ^ 3 + 0 * u ^ 2 + (z * t + x) * u + (t ^ 3 + y * t) from
        funext fun u => by simp only [hyperbolicUmbilicPotential]; ring, s36a_deriv_cubic]
  funext u; ring

lemma s36a_H_dt (s : ℂ) (x y z : ℝ) :
    deriv (fun u => hyperbolicUmbilicPotential s u x y z) =
      fun u => 3 * u ^ 2 + z * s + y := by
  rw [show (fun u => hyperbolicUmbilicPotential s u x y z) = fun u : ℂ =>
      1 * u ^ 3 + 0 * u ^ 2 + (z * s + y) * u + (s ^ 3 + x * s) from
        funext fun u => by simp only [hyperbolicUmbilicPotential]; ring, s36a_deriv_cubic]
  funext u; ring

lemma s36a_deriv_affine (a b : ℂ) : deriv (fun u : ℂ => a * u + b) = fun _ => a := by
  rw [show (fun u : ℂ => a * u + b) = fun u : ℂ => 0 * u ^ 3 + 0 * u ^ 2 + a * u + b from
    funext fun u => by ring, s36a_deriv_cubic]
  funext u; ring

lemma s36a_deriv_quad (a b c : ℂ) :
    deriv (fun u : ℂ => a * u ^ 2 + b * u + c) = fun u => 2 * a * u + b := by
  rw [show (fun u : ℂ => a * u ^ 2 + b * u + c) = fun u : ℂ => 0 * u ^ 3 + a * u ^ 2 + b * u + c
    from funext fun u => by ring, s36a_deriv_cubic]
  funext u; ring

lemma s36a_E_crit (s t : ℂ) (x y z : ℝ) :
    IsCriticalPoint₂ (fun s t => ellipticUmbilicPotential s t x y z) s t ↔
      3 * s ^ 2 - 3 * t ^ 2 + 2 * z * s + x = 0 ∧ -6 * s * t + 2 * z * t + y = 0 := by
  simp only [IsCriticalPoint₂, s36a_E_ds, s36a_E_dt]

lemma s36a_H_crit (s t : ℂ) (x y z : ℝ) :
    IsCriticalPoint₂ (fun s t => hyperbolicUmbilicPotential s t x y z) s t ↔
      3 * s ^ 2 + z * t + x = 0 ∧ 3 * t ^ 2 + z * s + y = 0 := by
  simp only [IsCriticalPoint₂, s36a_H_ds, s36a_H_dt]

lemma s36a_E_hess (s t : ℂ) (x y z : ℝ) :
    hessianDet₂ (fun s t => ellipticUmbilicPotential s t x y z) s t =
      4 * z ^ 2 - 36 * (s ^ 2 + t ^ 2) := by
  simp only [hessianDet₂, s36a_E_ds, s36a_E_dt]
  have h1 := s36a_deriv_quad 3 (2 * z) (-3 * t ^ 2 + x)
  have h2 := s36a_deriv_affine (-6 * s + 2 * z) y
  have h3 := s36a_deriv_affine (-6 * t) (2 * z * t + y)
  rw [show (fun u : ℂ => 3 * u ^ 2 - 3 * t ^ 2 + 2 * z * u + x) =
      fun u => 3 * u ^ 2 + 2 * z * u + (-3 * t ^ 2 + x) by funext u; ring, h1,
    show (fun u : ℂ => -6 * s * u + 2 * z * u + y) = fun u => (-6 * s + 2 * z) * u + y by
      funext u; ring, h2,
    show (fun u : ℂ => -6 * u * t + 2 * z * t + y) = fun u => -6 * t * u + (2 * z * t + y) by
      funext u; ring, h3]
  ring

lemma s36a_H_hess (s t : ℂ) (x y z : ℝ) :
    hessianDet₂ (fun s t => hyperbolicUmbilicPotential s t x y z) s t = 36 * s * t - z ^ 2 := by
  simp only [hessianDet₂, s36a_H_ds, s36a_H_dt]
  have h1 := s36a_deriv_quad 3 0 (z * t + x)
  have h2 := s36a_deriv_quad 3 0 (z * s + y)
  have h3 := s36a_deriv_affine z (3 * t ^ 2 + y)
  rw [show (fun u : ℂ => 3 * u ^ 2 + z * t + x) = fun u => 3 * u ^ 2 + 0 * u + (z * t + x) by
      funext u; ring, h1,
    show (fun u : ℂ => 3 * u ^ 2 + z * s + y) = fun u => 3 * u ^ 2 + 0 * u + (z * s + y) by
      funext u; ring, h2,
    show (fun u : ℂ => 3 * t ^ 2 + z * u + y) = fun u => z * u + (3 * t ^ 2 + y) by
      funext u; ring, h3]
  ring

/-! ### Cuspoid bifurcation sets (36.4.5–36.4.9) -/

/-- The fold bifurcation set is the origin `x = 0` (DLMF 36.4.5, `K = 1`). -/
@[dlmf 36.4.E5]
theorem cuspoidBifurcationSet_one : cuspoidBifurcationSet 1 = {x | x 0 = 0} := by
  ext x
  simp only [cuspoidBifurcationSet, Set.mem_ofPred_eq, (s36a_fold_derivs x _).1,
    (s36a_fold_derivs x _).2]
  constructor
  · rintro ⟨t, h1, h2⟩
    have ht : (t : ℂ) = 0 := by simpa using h2
    rw [ht] at h1
    exact_mod_cast (by simpa using h1 : (x 0 : ℂ) = 0)
  · intro h
    exact ⟨0, by simp [h], by simp⟩

/-- The cusp bifurcation set is the semicubical parabola `27x² = -8y³` (DLMF 36.4.6, `K = 2`,
with `x = x 0`, `y = x 1`). -/
@[dlmf 36.4.E6]
theorem cuspoidBifurcationSet_two :
    cuspoidBifurcationSet 2 = {x | 27 * x 0 ^ 2 = -8 * x 1 ^ 3} := by
  ext x
  simp only [cuspoidBifurcationSet, Set.mem_ofPred_eq, (s36a_cusp_derivs x _).1,
    (s36a_cusp_derivs x _).2]
  constructor
  · rintro ⟨t, h1, h2⟩
    have h1' : 4 * t ^ 3 + 2 * x 1 * t + x 0 = 0 := by exact_mod_cast h1
    have h2' : 12 * t ^ 2 + 2 * x 1 = 0 := by exact_mod_cast h2
    have hy : x 1 = -6 * t ^ 2 := by linarith
    have hx : x 0 = 8 * t ^ 3 := by rw [hy] at h1'; linarith
    rw [hx, hy]; ring
  · intro h
    by_cases hy : x 1 = 0
    · have hx : x 0 = 0 := by rw [hy] at h; simpa using h
      exact ⟨0, by simp [hx], by simp [hy]⟩
    · have hc : 27 * x 0 ^ 2 + 8 * x 1 ^ 3 = 0 := by linarith
      refine ⟨-3 * x 0 / (4 * x 1), ?_, ?_⟩
      · have : 4 * (-3 * x 0 / (4 * x 1)) ^ 3 + 2 * x 1 * (-3 * x 0 / (4 * x 1)) + x 0 =
            -(x 0) * (27 * x 0 ^ 2 + 8 * x 1 ^ 3) / (16 * x 1 ^ 3) := by
          field_simp; ring
        rw [hc, mul_zero, zero_div] at this
        exact_mod_cast this
      · have : 12 * (-3 * x 0 / (4 * x 1)) ^ 2 + 2 * x 1 =
            (27 * x 0 ^ 2 + 8 * x 1 ^ 3) / (4 * x 1 ^ 2) := by
          field_simp; ring
        rw [hc, zero_div] at this
        exact_mod_cast this

lemma s36a_swallowtail_crit (x : Fin 3 → ℝ) (t : ℝ) :
    (deriv (fun u => cuspoidPotential 3 u x) (t : ℂ) = 0 ∧
      iteratedDeriv 2 (fun u => cuspoidPotential 3 u x) (t : ℂ) = 0) ↔
      x 0 = 3 * t ^ 2 * (x 2 + 5 * t ^ 2) ∧ x 1 = -t * (3 * x 2 + 10 * t ^ 2) := by
  rw [(s36a_swallowtail_derivs x _).1, (s36a_swallowtail_derivs x _).2.1]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : 5 * t ^ 4 + 3 * x 2 * t ^ 2 + 2 * x 1 * t + x 0 = 0 := by exact_mod_cast h1
    have h2' : 20 * t ^ 3 + 6 * x 2 * t + 2 * x 1 = 0 := by exact_mod_cast h2
    constructor
    · linear_combination h1' - t * h2'
    · linear_combination h2' / 2
  · rintro ⟨hx, hy⟩
    constructor
    · have : 5 * t ^ 4 + 3 * x 2 * t ^ 2 + 2 * x 1 * t + x 0 = 0 := by rw [hx, hy]; ring
      exact_mod_cast this
    · have : 20 * t ^ 3 + 6 * x 2 * t + 2 * x 1 = 0 := by rw [hy]; ring
      exact_mod_cast this

/-- The swallowtail bifurcation set in parametric form (DLMF 36.4.7, `K = 3`, with
`(x, y, z) = (x 0, x 1, x 2)`): `x = 3t²(z + 5t²)`, `y = -t(3z + 10t²)`, `-∞ < t < ∞`. -/
@[dlmf 36.4.E7]
theorem cuspoidBifurcationSet_three :
    cuspoidBifurcationSet 3 =
      {x | ∃ t : ℝ, x 0 = 3 * t ^ 2 * (x 2 + 5 * t ^ 2) ∧ x 1 = -t * (3 * x 2 + 10 * t ^ 2)} := by
  ext x
  simp only [cuspoidBifurcationSet, Set.mem_ofPred_eq, s36a_swallowtail_crit]

/-- The self-intersection line of the swallowtail bifurcation set (DLMF 36.4.8): `y = 0`,
`z < 0`, `x = 9z²/20`. DLMF prints `z ≤ 0`; at `z = 0` the two degenerate critical points
coincide (`t = 0`), so the origin is a limit point of the self-intersection line rather than a
point at which two distinct degenerate critical points exist. -/
@[dlmf 36.4.E8]
theorem cuspoidSelfIntersection_three :
    cuspoidSelfIntersection 3 = {x | x 1 = 0 ∧ x 2 < 0 ∧ x 0 = 9 / 20 * x 2 ^ 2} := by
  ext x
  simp only [cuspoidSelfIntersection, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t₁, t₂, hne, h1, h2, h3, h4⟩
    obtain ⟨hx1, hy1⟩ := (s36a_swallowtail_crit x t₁).1 ⟨h1, h2⟩
    obtain ⟨hx2, hy2⟩ := (s36a_swallowtail_crit x t₂).1 ⟨h3, h4⟩
    have hsub : t₁ - t₂ ≠ 0 := sub_ne_zero.2 hne
    have hA : (t₁ - t₂) * (3 * x 2 + 10 * (t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2)) = 0 := by
      linear_combination hy1 - hy2
    have hA' := (mul_eq_zero.1 hA).resolve_left hsub
    have hB : (t₁ - t₂) * ((t₁ + t₂) * (3 * x 2 + 15 * (t₁ ^ 2 + t₂ ^ 2))) = 0 := by
      linear_combination hx2 - hx1
    rcases mul_eq_zero.1 ((mul_eq_zero.1 hB).resolve_left hsub) with hp | hq
    · have h₂ : t₂ = -t₁ := by linarith
      subst h₂
      have ht : t₁ ≠ 0 := by rintro rfl; simp at hne
      have hz : x 2 = -10 / 3 * t₁ ^ 2 := by linarith
      have hpos : 0 < t₁ ^ 2 := by positivity
      refine ⟨by rw [hy1, hz]; ring, by rw [hz]; linarith, by rw [hx1, hz]; ring⟩
    · exfalso
      have : 5 * (t₁ - t₂) ^ 2 = 0 := by linear_combination hq - hA'
      exact hsub (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith))
  · rintro ⟨hy, hz, hx⟩
    set t := Real.sqrt (-3 * x 2 / 10)
    have ht2 : t ^ 2 = -3 * x 2 / 10 := Real.sq_sqrt (by linarith)
    have htpos : 0 < t := Real.sqrt_pos.2 (by linarith)
    have key : ∀ u : ℝ, u ^ 2 = t ^ 2 →
        x 0 = 3 * u ^ 2 * (x 2 + 5 * u ^ 2) ∧ x 1 = -u * (3 * x 2 + 10 * u ^ 2) := by
      intro u hu
      rw [hu, ht2, hx, hy]; constructor <;> ring
    obtain ⟨a1, a2⟩ := (s36a_swallowtail_crit x t).2 (key t rfl)
    obtain ⟨b1, b2⟩ := (s36a_swallowtail_crit x (-t)).2 (key (-t) (by ring))
    refine ⟨t, -t, by linarith, a1, a2, ?_, ?_⟩ <;> push_cast at b1 b2 ⊢ <;> assumption

/-- The cusp lines (ribs) of the swallowtail bifurcation set (DLMF 36.4.9): `z ≤ 0`,
`x = -3z²/20`, `10y² = -4z³`. -/
@[dlmf 36.4.E9]
theorem cuspoidCuspLines_three :
    cuspoidCuspLines 3 =
      {x | x 2 ≤ 0 ∧ x 0 = -3 / 20 * x 2 ^ 2 ∧ 10 * x 1 ^ 2 = -4 * x 2 ^ 3} := by
  ext x
  simp only [cuspoidCuspLines, Set.mem_ofPred_eq, (s36a_swallowtail_derivs x _).2.2]
  constructor
  · rintro ⟨t, h1, h2, h3⟩
    obtain ⟨hx, hy⟩ := (s36a_swallowtail_crit x t).1 ⟨h1, h2⟩
    have h3' : 60 * t ^ 2 + 6 * x 2 = 0 := by exact_mod_cast h3
    have hz : x 2 = -10 * t ^ 2 := by linarith
    refine ⟨by rw [hz]; nlinarith [sq_nonneg t], by rw [hx, hz]; ring, ?_⟩
    rw [hy, hz]; ring
  · rintro ⟨hz, hx, hy⟩
    rcases hz.lt_or_eq with hz | hz
    · have hne : x 2 ≠ 0 := hz.ne
      have ht2 : (-x 1 / (2 * x 2)) ^ 2 = -x 2 / 10 := by
        field_simp; linear_combination hy
      have hc : x 0 = 3 * (-x 1 / (2 * x 2)) ^ 2 * (x 2 + 5 * (-x 1 / (2 * x 2)) ^ 2) ∧
          x 1 = -(-x 1 / (2 * x 2)) * (3 * x 2 + 10 * (-x 1 / (2 * x 2)) ^ 2) := by
        rw [ht2, hx]
        constructor
        · ring
        · field_simp; ring
      obtain ⟨h1, h2⟩ := (s36a_swallowtail_crit x _).2 hc
      refine ⟨-x 1 / (2 * x 2), h1, h2, ?_⟩
      have : 60 * (-x 1 / (2 * x 2)) ^ 2 + 6 * x 2 = 0 := by rw [ht2]; ring
      exact_mod_cast this
    · have hy0 : x 1 = 0 := by
        rw [hz] at hy; simpa using hy
      obtain ⟨h1, h2⟩ := (s36a_swallowtail_crit x 0).2 ⟨by rw [hx, hz]; ring, by rw [hy0]; ring⟩
      exact ⟨0, h1, h2, by simp [hz]⟩

/-! ### Umbilic bifurcation sets (36.4.10–36.4.13) -/

lemma s36a_E_bif_real (x y z : ℝ) :
    (x, y, z) ∈ umbilicBifurcationSet ellipticUmbilicPotential ↔
      ∃ s t : ℝ, 3 * s ^ 2 - 3 * t ^ 2 + 2 * z * s + x = 0 ∧ -6 * s * t + 2 * z * t + y = 0 ∧
        4 * z ^ 2 - 36 * (s ^ 2 + t ^ 2) = 0 := by
  simp only [umbilicBifurcationSet, Set.mem_ofPred_eq, s36a_E_crit, s36a_E_hess, and_assoc]
  norm_cast

lemma s36a_H_bif_real (x y z : ℝ) :
    (x, y, z) ∈ umbilicBifurcationSet hyperbolicUmbilicPotential ↔
      ∃ s t : ℝ, 3 * s ^ 2 + z * t + x = 0 ∧ 3 * t ^ 2 + z * s + y = 0 ∧
        36 * s * t - z ^ 2 = 0 := by
  simp only [umbilicBifurcationSet, Set.mem_ofPred_eq, s36a_H_crit, s36a_H_hess, and_assoc]
  norm_cast

lemma s36a_iteratedDeriv_three_cubic (a b c d : ℂ) :
    iteratedDeriv 3 (fun l : ℂ => a * l ^ 3 + b * l ^ 2 + c * l + d) = fun _ => 6 * a := by
  rw [s36a_iteratedDeriv_three, s36a_deriv_cubic, s36a_deriv_quad, s36a_deriv_affine]
  funext l; ring

lemma s36a_deriv_quad_zero (a b c : ℂ) : deriv (fun u : ℂ => a * u ^ 2 + b * u + c) 0 = b := by
  rw [s36a_deriv_quad]; ring

lemma s36a_E_cusp_real (x y z : ℝ) :
    (x, y, z) ∈ umbilicCuspLines ellipticUmbilicPotential ↔
      ∃ s t u v : ℝ, (u, v) ≠ (0, 0) ∧
        (3 * s ^ 2 - 3 * t ^ 2 + 2 * z * s + x = 0 ∧ -6 * s * t + 2 * z * t + y = 0) ∧
        6 * s * u - 6 * t * v + 2 * z * u = 0 ∧ -6 * s * v - 6 * t * u + 2 * z * v = 0 ∧
        6 * (u * (u ^ 2 - 3 * v ^ 2)) = 0 := by
  have e : ∀ s t u v : ℝ,
      (deriv (fun l : ℂ => deriv (fun w => ellipticUmbilicPotential w (t + l * v) x y z)
          (s + l * u)) 0 = 6 * s * u - 6 * t * v + 2 * z * u) ∧
      (deriv (fun l : ℂ => deriv (fun w => ellipticUmbilicPotential (s + l * u) w x y z)
          (t + l * v)) 0 = -6 * s * v - 6 * t * u + 2 * z * v) ∧
      (iteratedDeriv 3 (fun l : ℂ => ellipticUmbilicPotential (s + l * u) (t + l * v) x y z) 0 =
          6 * (u * (u ^ 2 - 3 * v ^ 2))) := by
    intro s t u v
    simp only [s36a_E_ds, s36a_E_dt]
    refine ⟨?_, ?_, ?_⟩
    · rw [show (fun l : ℂ => 3 * (s + l * u) ^ 2 - 3 * (t + l * v) ^ 2 + 2 * z * (s + l * u) + x)
          = fun l : ℂ => (3 * u ^ 2 - 3 * v ^ 2 : ℂ) * l ^ 2 + (6 * s * u - 6 * t * v + 2 * z * u)
            * l + (3 * s ^ 2 - 3 * t ^ 2 + 2 * z * s + x) from funext fun l => by ring,
        s36a_deriv_quad_zero]
    · rw [show (fun l : ℂ => -6 * (s + l * u) * (t + l * v) + 2 * z * (t + l * v) + y)
          = fun l : ℂ => (-6 * u * v : ℂ) * l ^ 2 + (-6 * s * v - 6 * t * u + 2 * z * v) * l +
            (-6 * s * t + 2 * z * t + y) from funext fun l => by ring, s36a_deriv_quad_zero]
    · rw [show (fun l : ℂ => ellipticUmbilicPotential (s + l * u) (t + l * v) x y z) =
          fun l : ℂ => ((u : ℂ) * (u ^ 2 - 3 * v ^ 2)) * l ^ 3 +
            (3 * s * u ^ 2 - 3 * s * v ^ 2 - 6 * t * u * v + u ^ 2 * z + v ^ 2 * z) * l ^ 2 +
            (3 * s ^ 2 * u - 6 * s * t * v + 2 * s * u * z - 3 * t ^ 2 * u + 2 * t * v * z +
              u * x + v * y) * l + ellipticUmbilicPotential s t x y z from
          funext fun l => by simp only [ellipticUmbilicPotential]; ring,
        s36a_iteratedDeriv_three_cubic]
  simp only [umbilicCuspLines, Set.mem_ofPred_eq, s36a_E_crit, e]
  norm_cast

lemma s36a_H_cusp_real (x y z : ℝ) :
    (x, y, z) ∈ umbilicCuspLines hyperbolicUmbilicPotential ↔
      ∃ s t u v : ℝ, (u, v) ≠ (0, 0) ∧
        (3 * s ^ 2 + z * t + x = 0 ∧ 3 * t ^ 2 + z * s + y = 0) ∧
        6 * s * u + z * v = 0 ∧ 6 * t * v + z * u = 0 ∧
        6 * ((u + v) * (u ^ 2 - u * v + v ^ 2)) = 0 := by
  have e : ∀ s t u v : ℝ,
      (deriv (fun l : ℂ => deriv (fun w => hyperbolicUmbilicPotential w (t + l * v) x y z)
          (s + l * u)) 0 = 6 * s * u + z * v) ∧
      (deriv (fun l : ℂ => deriv (fun w => hyperbolicUmbilicPotential (s + l * u) w x y z)
          (t + l * v)) 0 = 6 * t * v + z * u) ∧
      (iteratedDeriv 3
          (fun l : ℂ => hyperbolicUmbilicPotential (s + l * u) (t + l * v) x y z) 0 =
          6 * ((u + v) * (u ^ 2 - u * v + v ^ 2))) := by
    intro s t u v
    simp only [s36a_H_ds, s36a_H_dt]
    refine ⟨?_, ?_, ?_⟩
    · rw [show (fun l : ℂ => 3 * (s + l * u) ^ 2 + z * (t + l * v) + x)
          = fun l : ℂ => (3 * u ^ 2 : ℂ) * l ^ 2 + (6 * s * u + z * v) * l +
            (3 * s ^ 2 + z * t + x) from funext fun l => by ring, s36a_deriv_quad_zero]
    · rw [show (fun l : ℂ => 3 * (t + l * v) ^ 2 + z * (s + l * u) + y)
          = fun l : ℂ => (3 * v ^ 2 : ℂ) * l ^ 2 + (6 * t * v + z * u) * l +
            (3 * t ^ 2 + z * s + y) from funext fun l => by ring, s36a_deriv_quad_zero]
    · rw [show (fun l : ℂ => hyperbolicUmbilicPotential (s + l * u) (t + l * v) x y z) =
          fun l : ℂ => (((u : ℂ) + v) * (u ^ 2 - u * v + v ^ 2)) * l ^ 3 +
            (3 * s * u ^ 2 + 3 * t * v ^ 2 + u * v * z) * l ^ 2 +
            (3 * s ^ 2 * u + s * v * z + 3 * t ^ 2 * v + t * u * z + u * x + v * y) * l +
              hyperbolicUmbilicPotential s t x y z from
          funext fun l => by simp only [hyperbolicUmbilicPotential]; ring,
        s36a_iteratedDeriv_three_cubic]
  simp only [umbilicCuspLines, Set.mem_ofPred_eq, s36a_H_crit, e]
  norm_cast

/-- The rib of the hyperbolic umbilic bifurcation set (DLMF 36.4.13): `x = y = -z²/4`. -/
@[dlmf 36.4.E13]
theorem umbilicCuspLines_hyperbolic :
    umbilicCuspLines hyperbolicUmbilicPotential =
      {p | p.1 = -p.2.2 ^ 2 / 4 ∧ p.2.1 = -p.2.2 ^ 2 / 4} := by
  ext ⟨x, y, z⟩
  rw [s36a_H_cusp_real, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, t, u, v, huv, ⟨h1, h2⟩, k1, k2, c⟩
    have hq : u ^ 2 - u * v + v ^ 2 ≠ 0 := by
      intro h0
      have hv : v = 0 := by nlinarith [sq_nonneg (2 * u - v), sq_nonneg v]
      have hu : u = 0 := by rw [hv] at h0; simpa using h0
      exact huv (by rw [hu, hv])
    have huv' : u = -v := by
      have := (mul_eq_zero.1 ((mul_eq_zero.1 c).resolve_left (by norm_num))).resolve_right hq
      linarith
    have hv : v ≠ 0 := by rintro rfl; exact huv (by simp [huv'])
    subst huv'
    have hs : s = z / 6 := by
      have : v * (z - 6 * s) = 0 := by linear_combination k1
      have := (mul_eq_zero.1 this).resolve_left hv; linarith
    have ht : t = z / 6 := by
      have : v * (6 * t - z) = 0 := by linear_combination k2
      have := (mul_eq_zero.1 this).resolve_left hv; linarith
    subst hs ht
    constructor <;> linarith
  · rintro ⟨hx, hy⟩
    simp only at hx hy
    exact ⟨z / 6, z / 6, 1, -1, by simp, ⟨by rw [hx]; ring, by rw [hy]; ring⟩, by ring, by ring,
      by ring⟩

lemma s36a_exp_two_mul (τ : ℝ) : Real.exp (2 * τ) = Real.exp τ ^ 2 := by
  rw [← Real.exp_nat_mul]; norm_num

lemma s36a_exp_neg_two_mul (τ : ℝ) : Real.exp (-2 * τ) = (Real.exp τ ^ 2)⁻¹ := by
  rw [show -2 * τ = -(2 * τ) by ring, Real.exp_neg, s36a_exp_two_mul]

/-- The hyperbolic umbilic bifurcation set for `z ≠ 0` (DLMF 36.4.12):
`x = -z²(e^{2τ} ± 2e^{-τ})/12`, `y = -z²(e^{-2τ} ± 2e^{τ})/12`, `-∞ < τ < ∞`, the sign `±` being
`c = ±1`. On the plane `z = 0` the bifurcation set consists of the two half-lines `x = 0, y ≤ 0`
and `y = 0, x ≤ 0`, which the parametrization (with DLMF's `τ = -∞`) does not describe; the
statement is therefore restricted to `z ≠ 0`. -/
@[dlmf 36.4.E12]
theorem umbilicBifurcationSet_hyperbolic {x y z : ℝ} (hz : z ≠ 0) :
    (x, y, z) ∈ umbilicBifurcationSet hyperbolicUmbilicPotential ↔
      ∃ (τ : ℝ) (c : ℝ), (c = 1 ∨ c = -1) ∧
        x = -1 / 12 * z ^ 2 * (Real.exp (2 * τ) + c * 2 * Real.exp (-τ)) ∧
        y = -1 / 12 * z ^ 2 * (Real.exp (-2 * τ) + c * 2 * Real.exp τ) := by
  rw [s36a_H_bif_real]
  simp only [s36a_exp_two_mul, s36a_exp_neg_two_mul, Real.exp_neg]
  constructor
  · rintro ⟨s, t, h1, h2, h3⟩
    have hs : s ≠ 0 := by rintro rfl; apply hz; nlinarith
    set r := 6 * s / z with hr
    have hr0 : r ≠ 0 := by rw [hr]; exact div_ne_zero (by simpa using hs) hz
    have hsr : s = z / 6 * r := by rw [hr]; field_simp
    have htr : t = z / 6 / r := by
      have : 36 * s * t = z ^ 2 := by linarith
      rw [hr]; field_simp; nlinarith
    obtain ⟨τ, c, hc, e1, e2⟩ : ∃ τ c : ℝ, (c = 1 ∨ c = -1) ∧ c * Real.exp τ = r ∧
        Real.exp τ ^ 2 = r ^ 2 := by
      rcases lt_or_gt_of_ne hr0 with h | h
      · refine ⟨Real.log (-r), -1, Or.inr rfl, ?_, ?_⟩ <;> rw [Real.exp_log (by linarith)] <;>
          ring
      · exact ⟨Real.log r, 1, Or.inl rfl, by rw [Real.exp_log h]; ring, by rw [Real.exp_log h]⟩
    have hE : Real.exp τ ≠ 0 := (Real.exp_pos τ).ne'
    have hc2 : c ^ 2 = 1 := by rcases hc with rfl | rfl <;> norm_num
    have e3 : c * (Real.exp τ)⁻¹ = r⁻¹ := by
      rw [← e1, mul_inv]; congr 1; rcases hc with rfl | rfl <;> norm_num
    refine ⟨τ, c, hc, ?_, ?_⟩
    · rw [show c * 2 * (Real.exp τ)⁻¹ = 2 * (c * (Real.exp τ)⁻¹) by ring, e3, e2]
      have hx : x = -3 * s ^ 2 - z * t := by linarith
      rw [hx, hsr, htr]; field_simp; ring
    · rw [show c * 2 * Real.exp τ = 2 * (c * Real.exp τ) by ring, e1, e2]
      have hy : y = -3 * t ^ 2 - z * s := by linarith
      rw [hy, hsr, htr]; field_simp; ring
  · rintro ⟨τ, c, hc, hx, hy⟩
    have hE : Real.exp τ ≠ 0 := (Real.exp_pos τ).ne'
    have hc2 : c ^ 2 = 1 := by rcases hc with rfl | rfl <;> norm_num
    refine ⟨c * (z / 6) * Real.exp τ, c * (z / 6) * (Real.exp τ)⁻¹, ?_, ?_, ?_⟩
    · rw [hx]; field_simp; linear_combination (36 * z ^ 2 * Real.exp τ ^ 3) * hc2
    · rw [hy]; field_simp; linear_combination (36 * z ^ 2) * hc2
    · field_simp; linear_combination (36 * z ^ 2) * hc2

lemma s36a_exists_angle {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ φ ∈ Icc 0 (2 * π), Real.cos φ = a ∧ Real.sin φ = b := by
  set w : ℂ := ⟨a, b⟩
  have hw : ‖w‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [w]; rw [← sq, ← sq, h, Real.sqrt_one]
  have hw0 : w ≠ 0 := by intro h0; rw [h0, norm_zero] at hw; exact zero_ne_one hw
  have hc : Real.cos (arg w) = a := by rw [Complex.cos_arg hw0, hw, div_one]
  have hs : Real.sin (arg w) = b := by rw [Complex.sin_arg, hw, div_one]
  by_cases h0 : 0 ≤ arg w
  · exact ⟨arg w, ⟨h0, by linarith [Complex.arg_le_pi w, Real.pi_pos]⟩, hc, hs⟩
  · refine ⟨arg w + 2 * π, ⟨by linarith [Complex.neg_pi_lt_arg w], by linarith⟩, ?_, ?_⟩
    · rw [Real.cos_add_two_pi, hc]
    · rw [Real.sin_add_two_pi, hs]

/-- The elliptic umbilic bifurcation set (DLMF 36.4.10): for each `z` it is the astroid-like
curve `x = z²(-cos 2φ - 2cos φ)/3`, `y = z²(sin 2φ - 2 sin φ)/3`, `0 ≤ φ ≤ 2π`. -/
@[dlmf 36.4.E10]
theorem umbilicBifurcationSet_elliptic :
    umbilicBifurcationSet ellipticUmbilicPotential =
      {p | ∃ φ ∈ Icc 0 (2 * π),
        p.1 = 1 / 3 * p.2.2 ^ 2 * (-Real.cos (2 * φ) - 2 * Real.cos φ) ∧
        p.2.1 = 1 / 3 * p.2.2 ^ 2 * (Real.sin (2 * φ) - 2 * Real.sin φ)} := by
  ext ⟨x, y, z⟩
  rw [s36a_E_bif_real, Set.mem_ofPred_eq]
  simp only [Real.cos_two_mul, Real.sin_two_mul]
  constructor
  · rintro ⟨s, t, h1, h2, h3⟩
    by_cases hz : z = 0
    · subst hz
      have hs : s = 0 := by nlinarith [sq_nonneg s, sq_nonneg t]
      have ht : t = 0 := by nlinarith [sq_nonneg s, sq_nonneg t]
      subst hs ht
      exact ⟨0, ⟨le_rfl, by positivity⟩, by linarith, by linarith⟩
    · obtain ⟨φ, hφ, hc, hs⟩ := s36a_exists_angle (a := 3 * s / z) (b := 3 * t / z) (by
        field_simp; linarith)
      refine ⟨φ, hφ, ?_, ?_⟩
      · have hsφ : s = z / 3 * Real.cos φ := by rw [hc]; field_simp
        have htφ : t = z / 3 * Real.sin φ := by rw [hs]; field_simp
        have hpy := Real.sin_sq_add_cos_sq φ
        rw [hsφ, htφ] at h1
        linear_combination h1 + (z ^ 2 / 3) * hpy
      · have hsφ : s = z / 3 * Real.cos φ := by rw [hc]; field_simp
        have htφ : t = z / 3 * Real.sin φ := by rw [hs]; field_simp
        rw [hsφ, htφ] at h2
        linear_combination h2
  · rintro ⟨φ, -, hx, hy⟩
    have hpy := Real.sin_sq_add_cos_sq φ
    refine ⟨z / 3 * Real.cos φ, z / 3 * Real.sin φ, ?_, ?_, ?_⟩
    · rw [hx]; linear_combination (-z ^ 2 / 3) * hpy
    · rw [hy]; ring
    · linear_combination (-4 * z ^ 2) * hpy

lemma s36a_E_rib_real (x y z : ℝ) :
    (x, y, z) ∈ umbilicCuspLines ellipticUmbilicPotential ↔
      (x = -z ^ 2 ∧ y = 0) ∨ (x = z ^ 2 / 2 ∧ y = -(Real.sqrt 3 / 2) * z ^ 2) ∨
        (x = z ^ 2 / 2 ∧ y = Real.sqrt 3 / 2 * z ^ 2) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [s36a_E_cusp_real]
  constructor
  · rintro ⟨s, t, u, v, huv, ⟨h1, h2⟩, k1, k2, c⟩
    rcases mul_eq_zero.1 ((mul_eq_zero.1 c).resolve_left (by norm_num)) with hu | hu
    · subst hu
      have hv : v ≠ 0 := by rintro rfl; exact huv rfl
      have ht : t = 0 := by
        have : t * v = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_right hv
      have hs : s = z / 3 := by
        have : v * (2 * z - 6 * s) = 0 := by linear_combination k2
        have := (mul_eq_zero.1 this).resolve_left hv; linarith
      subst ht hs
      left; constructor <;> linarith
    · have hv : v ≠ 0 := by
        rintro rfl
        have : u = 0 := by simpa using hu
        exact huv (by rw [this])
      have hs : s = -z / 6 := by
        have : v ^ 2 * (24 * s + 4 * z) = 0 := by
          linear_combination u * k1 - v * k2 - (6 * s + 2 * z) * hu
        have := (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hv); linarith
      subst hs
      have ht : t = u * z / (6 * v) := by
        field_simp; linear_combination -k1
      have hr : (u / v) ^ 2 = Real.sqrt 3 ^ 2 := by
        rw [h3, div_pow]; field_simp; linarith
      have hx : x = z ^ 2 / 2 := by
        have ht2 : t ^ 2 = z ^ 2 / 12 := by
          rw [ht, show u * z / (6 * v) = u / v * z / 6 by field_simp, div_pow, mul_pow, hr, h3]
          ring
        linear_combination h1 + 3 * ht2
      have hy : y = -(u / v) * z ^ 2 / 2 := by
        have : y = -3 * z * t := by linarith
        rw [this, ht]; field_simp; ring
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hr with h | h
      · right; left; exact ⟨hx, by rw [hy, h]; ring⟩
      · right; right; exact ⟨hx, by rw [hy, h]; ring⟩
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact ⟨z / 3, 0, 0, 1, by simp, ⟨by rw [hx]; ring, by rw [hy]; ring⟩, by ring, by ring,
        by ring⟩
    · refine ⟨-z / 6, Real.sqrt 3 * z / 6, Real.sqrt 3, 1, by simp, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [hx]; linear_combination (-z ^ 2 / 12) * h3
      · rw [hy]; ring
      · ring
      · linear_combination (-z) * h3
      · linear_combination (0 : ℝ) * h3 + 6 * Real.sqrt 3 * h3
    · refine ⟨-z / 6, -(Real.sqrt 3 * z / 6), -Real.sqrt 3, 1, by simp, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [hx]; linear_combination (-z ^ 2 / 12) * h3
      · rw [hy]; ring
      · ring
      · linear_combination (-z) * h3
      · linear_combination -6 * Real.sqrt 3 * h3

lemma s36a_exp_two_thirds_pi (m : Fin 3) :
    Complex.exp (2 / 3 * I * π * ((m : ℕ) : ℂ)) =
      ![1, -1 / 2 + Real.sqrt 3 / 2 * I, -1 / 2 - Real.sqrt 3 / 2 * I] m := by
  fin_cases m
  · simp
  · have hc : Real.cos (2 / 3 * π) = -1 / 2 := by
      rw [show 2 / 3 * π = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
    have hs : Real.sin (2 / 3 * π) = Real.sqrt 3 / 2 := by
      rw [show 2 / 3 * π = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
    show Complex.exp (2 / 3 * I * π * ((1 : ℕ) : ℂ)) = -1 / 2 + Real.sqrt 3 / 2 * I
    rw [show 2 / 3 * I * π * ((1 : ℕ) : ℂ) = ((2 / 3 * π : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
    simp
  · have hc : Real.cos (4 / 3 * π) = -1 / 2 := by
      rw [show 4 / 3 * π = π / 3 + π by ring, Real.cos_add_pi, Real.cos_pi_div_three]; norm_num
    have hs : Real.sin (4 / 3 * π) = -(Real.sqrt 3 / 2) := by
      rw [show 4 / 3 * π = π / 3 + π by ring, Real.sin_add_pi, Real.sin_pi_div_three]
    show Complex.exp (2 / 3 * I * π * ((2 : ℕ) : ℂ)) = -1 / 2 - Real.sqrt 3 / 2 * I
    rw [show 2 / 3 * I * π * ((2 : ℕ) : ℂ) = ((4 / 3 * π : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
    simp; ring

/-- The ribs of the elliptic umbilic bifurcation set (DLMF 36.4.11): the three lines
`x + iy = -z² exp(2πim/3)`, `m = 0, 1, 2`. -/
@[dlmf 36.4.E11]
theorem umbilicCuspLines_elliptic :
    umbilicCuspLines ellipticUmbilicPotential =
      {p | ∃ m : Fin 3, (p.1 : ℂ) + I * p.2.1 =
        -(p.2.2 : ℂ) ^ 2 * Complex.exp (2 / 3 * I * π * ((m : ℕ) : ℂ))} := by
  ext ⟨x, y, z⟩
  rw [s36a_E_rib_real, Set.mem_ofPred_eq]
  have hre : ((z : ℂ) ^ 2).re = z ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have him : ((z : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
  simp only [s36a_exp_two_thirds_pi, Fin.exists_fin_succ, Fin.exists_fin_zero, Complex.ext_iff]
  simp [hre, him]
  constructor
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · left; exact ⟨hx, hy⟩
    · right; left; constructor <;> [rw [hx]; rw [hy]] <;> ring
    · right; right; constructor <;> [rw [hx]; rw [hy]] <;> ring
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · left; exact ⟨hx, hy⟩
    · right; left; constructor <;> [rw [hx]; rw [hy]] <;> ring
    · right; right; constructor <;> [rw [hx]; rw [hy]] <;> ring

/-! ### Number of real critical points (36.4.1, 36.4.2) -/

/-- A set mapped injectively into the zero set of a nonzero complex polynomial of degree at
most `n` is finite with at most `n` elements. -/
lemma q2s_finite_ncard_le_of_poly {α : Type*} {S : Set α} (f : α → ℂ) (hf : InjOn f S)
    {p : ℂ[X]} (hp : p ≠ 0) {n : ℕ} (hdeg : p.natDegree ≤ n)
    (hS : ∀ a ∈ S, p.eval (f a) = 0) : S.Finite ∧ S.ncard ≤ n := by
  have hm : MapsTo f S (p.roots.toFinset : Set ℂ) := fun a ha => by
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact (mem_roots hp).mpr (hS a ha)
  refine ⟨Set.Finite.of_injOn hm hf (Finset.finite_toSet _), ?_⟩
  calc S.ncard ≤ (p.roots.toFinset : Set ℂ).ncard :=
        Set.ncard_le_ncard_of_injOn f hm hf (Finset.finite_toSet _)
    _ = p.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p
    _ ≤ n := hdeg

/-- The derivative polynomial of the cuspoid potential. -/
lemma q2s_cuspoid_deriv_eq (K : ℕ) (x : Fin K → ℝ) (t : ℂ) :
    deriv (fun u => cuspoidPotential K u x) t =
      (C ((K : ℂ) + 2) * X ^ (K + 1) +
        ∑ m : Fin K, C ((((m : ℕ) : ℂ) + 1) * (x m : ℂ)) * X ^ (m : ℕ)).eval t := by
  have h : HasDerivAt (fun u => cuspoidPotential K u x)
      (((K + 2 : ℕ) : ℂ) * t ^ (K + 2 - 1) +
        ∑ m : Fin K, (x m : ℂ) * (((m : ℕ) + 1 : ℕ) * t ^ ((m : ℕ) + 1 - 1))) t := by
    unfold cuspoidPotential
    exact (hasDerivAt_pow _ t).add (HasDerivAt.fun_sum fun m _ =>
      (hasDerivAt_pow _ t).const_mul _)
  rw [h.deriv]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_finsetSum]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma q2s_E_crit_real (x y z : ℝ) (p : ℝ × ℝ) :
    p ∈ umbilicCriticalPoints ellipticUmbilicPotential x y z ↔
      3 * (p.1 : ℂ) ^ 2 - 3 * (p.2 : ℂ) ^ 2 + 2 * z * p.1 + x = 0 ∧
        -6 * (p.1 : ℂ) * p.2 + 2 * z * p.2 + y = 0 :=
  s36a_E_crit _ _ x y z

lemma q2s_H_crit_real (x y z : ℝ) (p : ℝ × ℝ) :
    p ∈ umbilicCriticalPoints hyperbolicUmbilicPotential x y z ↔
      3 * (p.1 : ℂ) ^ 2 + z * p.2 + x = 0 ∧ 3 * (p.2 : ℂ) ^ 2 + z * p.1 + y = 0 :=
  s36a_H_crit _ _ x y z

/-- The real roots of a quadratic `3s² + c` (`c` real) number at most two. -/
lemma q2s_quadratic_roots (c : ℝ) :
    {s : ℝ | 3 * (s : ℂ) ^ 2 + c = 0}.Finite ∧ {s : ℝ | 3 * (s : ℂ) ^ 2 + c = 0}.ncard ≤ 2 := by
  refine q2s_finite_ncard_le_of_poly (fun s : ℝ => (s : ℂ)) ofReal_injective.injOn
    (p := C 3 * X ^ 2 + C (c : ℂ)) ?_ ?_ ?_
  · intro h
    have := congrArg (fun q => q.coeff 2) h
    simp at this
  · compute_degree!
  · intro s hs; simpa using hs

lemma q2s_E_count (x y z : ℝ) :
    (umbilicCriticalPoints ellipticUmbilicPotential x y z).Finite ∧
      (umbilicCriticalPoints ellipticUmbilicPotential x y z).ncard ≤ 4 := by
  have hinj : InjOn (fun p : ℝ × ℝ => (p.1 : ℂ) + I * p.2)
      (umbilicCriticalPoints ellipticUmbilicPotential x y z) := by
    intro p _ q _ h
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp at h1 h2
    exact Prod.ext h1 h2
  set w : ℂ := (x : ℂ) - I * y
  by_cases hz : z = 0
  · refine q2s_finite_ncard_le_of_poly _ hinj (p := C 3 * X ^ 2 + C w) ?_ ?_ ?_
    · intro h
      have := congrArg (fun q => q.coeff 2) h
      simp at this
    · compute_degree!
    · intro p hp
      rw [q2s_E_crit_real] at hp
      obtain ⟨h1, h2⟩ := hp
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, w]
      rw [hz] at h1 h2; push_cast at h1 h2
      linear_combination h1 - I * h2 + (3 * (p.2 : ℂ) ^ 2) * I_sq
  · have hz' : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz
    refine q2s_finite_ncard_le_of_poly _ hinj
      (p := C (27 : ℂ) * X ^ 4 + C (18 * w) * X ^ 2 + C (8 * (z : ℂ) ^ 3) * X +
        C (3 * w ^ 2 + 4 * (z : ℂ) ^ 2 * (starRingEnd ℂ w))) ?_ ?_ ?_
    · intro h
      have := congrArg (fun q => q.coeff 4) h
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at this
      norm_num at this
    · compute_degree!
    · intro p hp
      rw [q2s_E_crit_real] at hp
      obtain ⟨h1, h2⟩ := hp
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      simp only [w, map_sub, map_mul, conj_I, conj_ofReal]
      -- with a = s + it, ā = s - it: 3a² + 2zā + w = E1 - iE2, 3ā² + 2za + w̄ = E1 + iE2
      set s : ℂ := (p.1 : ℂ)
      set t : ℂ := (p.2 : ℂ)
      have hA : 3 * (s + I * t) ^ 2 + 2 * z * (s - I * t) + (x - I * y) = 0 := by
        linear_combination h1 - I * h2 + (3 * t ^ 2) * I_sq
      have hB : 3 * (s - I * t) ^ 2 + 2 * z * (s + I * t) + (x + I * y) = 0 := by
        linear_combination h1 + I * h2 + (3 * t ^ 2) * I_sq
      linear_combination (3 * (3 * (s + I * t) ^ 2 + (x - I * y)) - 6 * z * (s - I * t)) * hA +
        4 * z ^ 2 * hB

lemma q2s_H_count (x y z : ℝ) :
    (umbilicCriticalPoints hyperbolicUmbilicPotential x y z).Finite ∧
      (umbilicCriticalPoints hyperbolicUmbilicPotential x y z).ncard ≤ 4 := by
  by_cases hz : z = 0
  · have hsub : umbilicCriticalPoints hyperbolicUmbilicPotential x y z ⊆
        {s : ℝ | 3 * (s : ℂ) ^ 2 + x = 0} ×ˢ {t : ℝ | 3 * (t : ℂ) ^ 2 + y = 0} := by
      intro p hp
      rw [q2s_H_crit_real, hz] at hp
      push_cast at hp
      simpa using hp
    obtain ⟨hA, hA'⟩ := q2s_quadratic_roots x
    obtain ⟨hB, hB'⟩ := q2s_quadratic_roots y
    refine ⟨(hA.prod hB).subset hsub, ?_⟩
    calc _ ≤ ({s : ℝ | 3 * (s : ℂ) ^ 2 + x = 0} ×ˢ {t : ℝ | 3 * (t : ℂ) ^ 2 + y = 0}).ncard :=
          Set.ncard_le_ncard hsub (hA.prod hB)
      _ = _ := Set.ncard_prod
      _ ≤ 2 * 2 := Nat.mul_le_mul hA' hB'
  · have hz' : (z : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz
    have hinj : InjOn (fun p : ℝ × ℝ => (p.1 : ℂ))
        (umbilicCriticalPoints hyperbolicUmbilicPotential x y z) := by
      intro p hp q hq h
      rw [q2s_H_crit_real] at hp hq
      simp only [ofReal_inj] at h
      have ht : (p.2 : ℂ) = q.2 := by
        have : (z : ℂ) * p.2 = z * q.2 := by
          rw [h] at hp; linear_combination hp.1 - hq.1
        exact mul_left_cancel₀ hz' this
      exact Prod.ext h (ofReal_inj.mp ht)
    refine q2s_finite_ncard_le_of_poly _ hinj
      (p := C (27 : ℂ) * X ^ 4 + C (18 * (x : ℂ)) * X ^ 2 + C ((z : ℂ) ^ 3) * X +
        C (3 * (x : ℂ) ^ 2 + (z : ℂ) ^ 2 * y)) ?_ ?_ ?_
    · intro h
      have := congrArg (fun q => q.coeff 4) h
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at this
      norm_num at this
    · compute_degree!
    · intro p hp
      rw [q2s_H_crit_real] at hp
      obtain ⟨h1, h2⟩ := hp
      simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
      linear_combination (3 * (3 * (p.1 : ℂ) ^ 2 + x) - 3 * z * p.2) * h1 + z ^ 2 * h2


/-- A cuspoid of codimension `K` has finitely many real critical points, at most `K + 1`
(DLMF 36.4.1: `1 ≤ j ≤ j_max(x) ≤ K + 1`). -/
@[dlmf 36.4.E1]
theorem cuspoidCriticalPoints_finite_ncard_le (K : ℕ) (x : Fin K → ℝ) :
    (cuspoidCriticalPoints K x).Finite ∧ (cuspoidCriticalPoints K x).ncard ≤ K + 1 := by
  set p : ℂ[X] := C ((K : ℂ) + 2) * X ^ (K + 1) +
    ∑ m : Fin K, C ((((m : ℕ) : ℂ) + 1) * (x m : ℂ)) * X ^ (m : ℕ) with hp
  have hcoeff : p.coeff (K + 1) = (K : ℂ) + 2 := by
    rw [hp, coeff_add, coeff_C_mul_X_pow, finsetSum_coeff, Finset.sum_eq_zero, add_zero]
    · simp only [↓reduceIte]
    intro m _
    rw [coeff_C_mul_X_pow]
    split_ifs with h
    · have := m.isLt; omega
    · rfl
  have hne : p ≠ 0 := by
    intro h
    rw [h, coeff_zero] at hcoeff
    have : ((K : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : K + 2 ≠ 0)
    exact this hcoeff.symm
  have hdeg : p.natDegree ≤ K + 1 := by
    rw [hp]
    refine natDegree_add_le_of_degree_le (natDegree_C_mul_X_pow_le _ _) ?_
    refine natDegree_sum_le_of_forall_le _ _ fun m _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by have := m.isLt; omega)
  refine q2s_finite_ncard_le_of_poly (fun t : ℝ => (t : ℂ)) ofReal_injective.injOn hne hdeg ?_
  intro t ht
  have : deriv (fun u => cuspoidPotential K u x) (t : ℂ) = 0 := ht
  rwa [q2s_cuspoid_deriv_eq] at this

/-- An umbilic catastrophe has finitely many real critical points, at most four
(DLMF 36.4.2: `1 ≤ j ≤ j_max(x) ≤ 4`). -/
@[dlmf 36.4.E2]
theorem umbilicCriticalPoints_finite_ncard_le (x y z : ℝ) :
    (umbilicCriticalPoints ellipticUmbilicPotential x y z).Finite ∧
      (umbilicCriticalPoints ellipticUmbilicPotential x y z).ncard ≤ 4 ∧
      (umbilicCriticalPoints hyperbolicUmbilicPotential x y z).Finite ∧
      (umbilicCriticalPoints hyperbolicUmbilicPotential x y z).ncard ≤ 4 :=
  ⟨(q2s_E_count x y z).1, (q2s_E_count x y z).2, (q2s_H_count x y z).1, (q2s_H_count x y z).2⟩

end DLMF.CoalescingSaddles
