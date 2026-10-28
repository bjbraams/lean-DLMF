/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Topology.Algebra.MvPolynomial
public import TauCeti.MeasureTheory.Constructions.HaarToSphere

/-!
# Harmonic polynomials (AAR §§9.1–9.5)

Mathlib has harmonic *functions* (`InnerProductSpace.HarmonicAt`) and the Laplacian, but
not the finite-dimensional spaces of homogeneous harmonic polynomials (spherical harmonics).
The orthogonality of harmonic polynomials of different degrees integrates by parts against the
Gaussian `exp (-‖x‖²)` with Mathlib's line-derivative integration by parts and Euler identity,
and passes to the sphere with the Tau Ceti contributors' polar-coordinate formula
`TauCeti.integral_eq_integral_Ioi_integral_toSphere`; the homogeneous scaling lemma is adapted
from their `MvPolynomial.IsHomogeneous.eval₂_const_mul`.
-/

@[expose] public section

open MvPolynomial
open scoped BigOperators

noncomputable section

namespace DLMF.SphericalHarmonics

/-- Laplacian on multivariate polynomials. -/
def laplacianMv {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, pderiv i (pderiv i p)

/-- Homogeneous harmonic polynomials of degree `k` in `n` variables. -/
def IsHarmonicHomogeneous {n : ℕ} (k : ℕ) (p : MvPolynomial (Fin n) ℝ) : Prop :=
  p.IsHomogeneous k ∧ laplacianMv p = 0

/-- The real surface inner product of polynomial restrictions to the Euclidean unit sphere,
AAR (9.4.4), p. 452. Mathlib's `Measure.toSphere` supplies surface measure from Lebesgue
measure. -/
def sphericalHarmonicInner {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) : ℝ :=
  ∫ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    eval (fun i => x.val i) p * eval (fun i => x.val i) q
      ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).toSphere

/-- The surface inner product has the unnormalized area `4π` in three dimensions,
as required by the coefficient in AAR's addition theorem. -/
theorem sphericalHarmonicInner_one_three :
    sphericalHarmonicInner (n := 3) 1 1 = 4 * Real.pi := by
  simp [sphericalHarmonicInner, MeasureTheory.measureReal_def,
    MeasureTheory.Measure.toSphere_apply_univ]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

/-- Combinatorial dimension of the space of harmonic homogeneous polynomials of
degree `k` in `n` variables (AAR §9.3): `\binom{n+k-1}{k} - \binom{n+k-3}{k-2}`. -/
def harmonicHomogeneousDim (n k : ℕ) : ℕ :=
  (n + k - 1).choose k - if 2 ≤ k then (n + k - 3).choose (k - 2) else 0

/-- In three variables the dimension is `2k + 1`. -/
theorem harmonicHomogeneousDim_three (k : ℕ) :
    harmonicHomogeneousDim 3 k = 2 * k + 1 := by
  -- Already follows from Mathlib's symmetry and Pascal identities for `Nat.choose`.
  unfold harmonicHomogeneousDim
  split_ifs with h
  · have h1 : 3 + k - 1 = k + 2 := by omega
    have h2 : 3 + k - 3 = k := by omega
    rw [h1, h2, Nat.choose_symm_add, Nat.choose_symm h]
    have hp := Nat.choose_succ_succ' (k + 1) 1
    have hq := Nat.choose_succ_succ' k 1
    norm_num [Nat.choose_one_right, Nat.add_assoc] at hp hq
    omega
  · have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> norm_num

/-- Constants are harmonic. -/
theorem laplacianMv_C {n : ℕ} (r : ℝ) : laplacianMv (C r : MvPolynomial (Fin n) ℝ) = 0 := by
  simp [laplacianMv]

/-- Every constant polynomial is a homogeneous harmonic polynomial of degree `0`. -/
theorem isHarmonicHomogeneous_C (n : ℕ) (r : ℝ) :
    IsHarmonicHomogeneous (n := n) 0 (C r) := by
  refine ⟨?_, laplacianMv_C r⟩
  exact MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) r

section Orthogonality

open MeasureTheory

/-- Coordinate line derivatives of polynomial functions on Euclidean space. -/
private lemma hhOrth_hasLineDerivAt {n : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    HasLineDerivAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => eval (fun j => y j) P)
      (eval (fun j => x j) (pderiv i P)) x (EuclideanSpace.single i 1) := by
  unfold HasLineDerivAt
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : ℝ) a
  | add p q hp hq =>
    have := hp.add hq
    simp only [map_add]
    exact this
  | mul_X p j hp =>
    have hj : HasDerivAt (fun t : ℝ => x j + t * (if j = i then 1 else 0))
        (if j = i then 1 else 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (if j = i then (1 : ℝ) else 0)).const_add (x j)
    have := hp.mul hj
    convert this using 1
    · funext t; simp
    · simp only [map_mul, Derivation.leibniz, pderiv_X, smul_eq_mul, eval_add, eval_X]
      rcases eq_or_ne i j with rfl | h
      · simp; ring
      · simp [Ne.symm h, mul_comm]

/-- The squared Euclidean norm as a polynomial. -/
private lemma hhOrth_norm_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = eval (fun j => x j) (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- Coordinate line derivatives of the Gaussian `exp (-‖x‖²)`. -/
private lemma hhOrth_hasLineDerivAt_gauss {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    HasLineDerivAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖y‖ ^ 2))
      (-(2 * x i) * Real.exp (-‖x‖ ^ 2)) x (EuclideanSpace.single i 1) := by
  have h := hhOrth_hasLineDerivAt (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2) x i
  have hd : eval (fun j => x j) (pderiv i (∑ j : Fin n, (X j : MvPolynomial (Fin n) ℝ) ^ 2)) =
      2 * x i := by
    simp [map_sum, Derivation.leibniz_pow, pderiv_X, Pi.single_apply]
  rw [hd] at h
  unfold HasLineDerivAt at h ⊢
  simp only [hhOrth_norm_sq]
  have := h.neg.exp
  convert this using 1
  simp only [Pi.neg_apply, zero_smul, add_zero]
  ring

/-- Polynomial growth of polynomial functions on Euclidean space. -/
private lemma hhOrth_bound {n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ d : ℕ, ∀ x : EuclideanSpace ℝ (Fin n),
      |eval (fun j => x j) P| ≤ K * (1 + ‖x‖) ^ d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨|a|, abs_nonneg a, 0, fun x => by simp⟩
  | add p q hp hq =>
    obtain ⟨K₁, hK₁, d₁, h₁⟩ := hp
    obtain ⟨K₂, hK₂, d₂, h₂⟩ := hq
    refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, d₁ + d₂, fun x => ?_⟩
    have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := le_add_of_nonneg_right (norm_nonneg x)
    have e1 : (1 + ‖x‖) ^ d₁ ≤ (1 + ‖x‖) ^ (d₁ + d₂) := pow_le_pow_right₀ h1 (by omega)
    have e2 : (1 + ‖x‖) ^ d₂ ≤ (1 + ‖x‖) ^ (d₁ + d₂) := pow_le_pow_right₀ h1 (by omega)
    rw [eval_add]
    calc |eval (fun j => x j) p + eval (fun j => x j) q|
        ≤ |eval (fun j => x j) p| + |eval (fun j => x j) q| := abs_add_le _ _
      _ ≤ K₁ * (1 + ‖x‖) ^ d₁ + K₂ * (1 + ‖x‖) ^ d₂ := add_le_add (h₁ x) (h₂ x)
      _ ≤ K₁ * (1 + ‖x‖) ^ (d₁ + d₂) + K₂ * (1 + ‖x‖) ^ (d₁ + d₂) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hK₁) (mul_le_mul_of_nonneg_left e2 hK₂)
      _ = (K₁ + K₂) * (1 + ‖x‖) ^ (d₁ + d₂) := by ring
  | mul_X p j hp =>
    obtain ⟨K, hK, d, h⟩ := hp
    refine ⟨K, hK, d + 1, fun x => ?_⟩
    have hj : |x j| ≤ 1 + ‖x‖ := by
      have := PiLp.norm_apply_le x j
      rw [Real.norm_eq_abs] at this
      linarith [norm_nonneg x]
    rw [eval_mul, eval_X, abs_mul, pow_succ, ← mul_assoc]
    exact mul_le_mul (h x) hj (abs_nonneg _) (mul_nonneg hK (by positivity))

/-- Polynomials times the Gaussian are integrable on Euclidean space. -/
private lemma hhOrth_integrable {n : ℕ} [Nontrivial (EuclideanSpace ℝ (Fin n))]
    (P : MvPolynomial (Fin n) ℝ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      eval (fun j => x j) P * Real.exp (-‖x‖ ^ 2)) := by
  obtain ⟨K, hK, d, h⟩ := hhOrth_bound P
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin n) => eval (fun j => x j) P :=
    (MvPolynomial.continuous_eval P).comp (PiLp.continuous_ofLp 2 _)
  have hg : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (fun r : ℝ => K * (1 + r) ^ d * Real.exp (-r ^ 2)) ‖x‖) := by
    rw [integrable_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (f := fun r : ℝ => K * (1 + r) ^ d * Real.exp (-r ^ 2))]
    have hfun : (fun y : ℝ => y ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1) •
        (K * (1 + y) ^ d * Real.exp (-y ^ 2))) = fun y => ∑ m ∈ Finset.range (d + 1),
          (K * (d.choose m : ℝ)) * (y ^ ((m + (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1)
            : ℕ) : ℝ) * Real.exp (-1 * y ^ 2)) := by
      funext y
      rw [smul_eq_mul, add_comm (1 : ℝ) y, add_pow]
      simp only [one_pow, mul_one, Real.rpow_natCast, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring_nf
    rw [hfun]
    exact integrable_finsetSum _ fun m _ =>
      (integrableOn_rpow_mul_exp_neg_mul_sq one_pos
        (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _))).const_mul _
  refine hg.mono' (hcont.mul (Real.continuous_exp.comp
    (continuous_norm.pow 2).neg)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (h x) (Real.exp_pos _).le

/-- Scaling the variables of a homogeneous polynomial; adapted from the Tau Ceti contributors'
`MvPolynomial.IsHomogeneous.eval₂_const_mul`. -/
private lemma hhOrth_eval_smul {n m : ℕ} {P : MvPolynomial (Fin n) ℝ} (hP : P.IsHomogeneous m)
    (r : ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    eval (fun j => (r • u) j) P = r ^ m * eval (fun j => u j) P := by
  exact hP.eval₂_const_mul (RingHom.id ℝ) (fun j => u j) r

/-- The polynomial identity behind the Gaussian integration by parts. -/
private lemma hhOrth_div {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) :
    ∑ i : Fin n, pderiv i (q * pderiv i p - p * pderiv i q) =
      q * laplacianMv p - p * laplacianMv q := by
  simp only [laplacianMv, map_sub, Derivation.leibniz, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Orthogonality of harmonic homogeneous polynomials of different degrees on the sphere
(AAR §9.4). -/
theorem harmonicHomogeneous_orthogonal {n k l : ℕ} {p q : MvPolynomial (Fin n) ℝ}
    (hp : IsHarmonicHomogeneous k p) (hq : IsHarmonicHomogeneous l q) (hkl : k ≠ l) :
    sphericalHarmonicInner p q = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (volume : Measure (EuclideanSpace ℝ (Fin 0))).toSphere = 0 :=
      (Measure.toSphere_eq_zero_iff _).2 inferInstance
    simp [sphericalHarmonicInner, h0]
  have : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    ⟨⟨EuclideanSpace.single ⟨0, hn⟩ 1, 0, by
      intro h; have := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x ⟨0, hn⟩) h; simp at this⟩⟩
  set G : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (-‖x‖ ^ 2) with hG
  set F : Fin n → MvPolynomial (Fin n) ℝ := fun i => q * pderiv i p - p * pderiv i q with hF
  set ev : MvPolynomial (Fin n) ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun P x => eval (fun j => x j) P with hev
  -- integration by parts in each coordinate direction
  have hIBP : ∀ i : Fin n, ∫ x, ev (F i) x * (-(2 * x i) * G x) =
      -∫ x, ev (pderiv i (F i)) x * G x := by
    intro i
    have h1 : Integrable fun x => ev (pderiv i (F i)) x * G x := hhOrth_integrable _
    have h2 : Integrable fun x => ev (F i) x * (-(2 * x i) * G x) := by
      refine (hhOrth_integrable (F i * (C (-2) * X i))).congr (Filter.Eventually.of_forall
        fun x => ?_)
      simp only [hev, eval_mul, eval_C, eval_X]; ring
    have h3 : Integrable fun x => ev (F i) x * G x := hhOrth_integrable _
    have := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (μ := volume) (B := ContinuousLinearMap.mul ℝ ℝ) (v := EuclideanSpace.single i 1)
      (f := ev (F i)) (f' := fun x => ev (pderiv i (F i)) x) (g := G)
      (g' := fun x => -(2 * x i) * G x) h1 h2 h3
      (fun x _ => hhOrth_hasLineDerivAt (F i) x i)
      (fun x _ => hhOrth_hasLineDerivAt_gauss x i)
    simpa using this
  -- summing over the directions
  have hkey : ((k : ℝ) - l) * ∫ x, ev (p * q) x * G x = 0 := by
    have hsum := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hIBP i
    rw [← integral_finsetSum _ fun i _ => (hhOrth_integrable (F i * (C (-2) * X i))).congr
        (Filter.Eventually.of_forall fun x => by simp only [hev, eval_mul, eval_C, eval_X]; ring),
      Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ => hhOrth_integrable _] at hsum
    have hL : ∀ x, ∑ i, ev (F i) x * (-(2 * x i) * G x) =
        -2 * (((k : ℝ) - l) * (ev (p * q) x * G x)) := by
      intro x
      have he := congrArg (eval fun j => x j) (hp.1.sum_X_mul_pderiv)
      have he' := congrArg (eval fun j => x j) (hq.1.sum_X_mul_pderiv)
      simp only [map_sum, eval_mul, eval_X, nsmul_eq_mul, map_natCast] at he he'
      simp only [hev, hF, map_sub, eval_mul]
      have : ∑ i, (eval (fun j => x j) q * eval (fun j => x j) (pderiv i p) -
          eval (fun j => x j) p * eval (fun j => x j) (pderiv i q)) * (-(2 * x i) * G x) =
          -2 * G x * (eval (fun j => x j) q * ∑ i, x i * eval (fun j => x j) (pderiv i p) -
            eval (fun j => x j) p * ∑ i, x i * eval (fun j => x j) (pderiv i q)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [this, he, he']
      ring
    have hR : ∀ x, ∑ i, ev (pderiv i (F i)) x * G x = 0 := by
      intro x
      rw [← Finset.sum_mul]
      have := congrArg (eval fun j => x j) (hhOrth_div p q)
      simp only [hp.2, hq.2, mul_zero, sub_zero, map_zero, map_sum] at this
      simp only [hev, hF, this, zero_mul]
    have e1 : (∫ a, ∑ i, ev (F i) a * (-(2 * a i) * G a)) =
        -2 * (((k : ℝ) - l) * ∫ x, ev (p * q) x * G x) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hL), integral_const_mul,
        integral_const_mul]
    have e2 : (∫ a, ∑ i, ev (pderiv i (F i)) a * G a) = 0 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hR), integral_zero]
    rw [e1, e2, neg_zero] at hsum
    linarith
  have hkl' : ((k : ℝ) - l) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hkl)
  have hint0 : ∫ x, ev (p * q) x * G x = 0 := (mul_eq_zero.1 hkey).resolve_left hkl'
  -- polar coordinates
  have hpolar := TauCeti.integral_eq_integral_Ioi_integral_toSphere (μ := volume)
    (fun x => ev (p * q) x * G x) (hhOrth_integrable (p * q))
  have hpq := hp.1.mul hq.1
  set N : ℕ := Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - 1 with hN
  have hin : ∀ r ∈ Set.Ioi (0 : ℝ), r ^ N • ∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      ev (p * q) (r • (u : EuclideanSpace ℝ (Fin n))) * G (r • (u : EuclideanSpace ℝ (Fin n)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere =
      (r ^ (N + (k + l)) * Real.exp (-1 * r ^ 2)) * sphericalHarmonicInner p q := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    have : ∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ev (p * q) (r • (u : EuclideanSpace ℝ (Fin n))) * G (r • (u : EuclideanSpace ℝ (Fin n))) =
        (r ^ (k + l) * Real.exp (-1 * r ^ 2)) *
          (eval (fun i => (u : EuclideanSpace ℝ (Fin n)) i) p *
            eval (fun i => (u : EuclideanSpace ℝ (Fin n)) i) q) := by
      intro u
      have hu : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := by simp
      simp only [hev, hG, hhOrth_eval_smul hpq, norm_smul, hu, Real.norm_eq_abs,
        abs_of_pos hr0, mul_one, eval_mul]
      ring_nf
    simp only [this, integral_const_mul, sphericalHarmonicInner, smul_eq_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_mul_const] at hpolar
  have hc : 0 < ∫ r in Set.Ioi (0 : ℝ), r ^ (N + (k + l)) * Real.exp (-1 * r ^ 2) := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := ((N + (k + l) : ℕ) : ℝ)) (b := 1)
      two_pos (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _)) one_pos
    have hcongr : ∫ r in Set.Ioi (0 : ℝ), r ^ (N + (k + l)) * Real.exp (-1 * r ^ 2) =
        ∫ r in Set.Ioi (0 : ℝ), r ^ (((N + (k + l) : ℕ) : ℝ)) * Real.exp (-1 * r ^ (2 : ℝ)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      simp only [Real.rpow_natCast, Real.rpow_two]
    rw [hcongr, h]
    have := Real.Gamma_pos_of_pos (show 0 < ((((N + (k + l) : ℕ) : ℝ)) + 1) / 2 by positivity)
    positivity
  have := hpolar.symm.trans hint0
  exact (mul_eq_zero.1 this).resolve_left hc.ne'

end Orthogonality

end DLMF.SphericalHarmonics
