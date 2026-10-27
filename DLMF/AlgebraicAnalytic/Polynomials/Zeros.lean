/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.AlgebraicAnalytic.Polynomials.Defs
public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.FieldTheory.GaloisGroups.Resolvent.Quartic.Discriminant

/-!
# Zeros of polynomials (DLMF §1.11)

Statements of DLMF §1.11 that are not already in Mathlib (the upstream ones are recorded in
`DLMF.AlgebraicAnalytic.Polynomials.MathlibCoverage`).

* §1.11(i): Horner's scheme (`hornerB`, 1.11.2–1.11.4) and the extended scheme (`hornerC`,
  1.11.5–1.11.6) for a polynomial `f ∈ K[X]` over a field.
* §1.11(ii): real zeros of monic real polynomials of odd and even degree, the parity part of
  Descartes' rule of signs and its form for negative zeros, reciprocal zeros, the discriminant as
  a product over the zeros (1.11.9).
* §1.11(iii): quadratic, cubic (Cardano) and quartic (Ferrari, with DLMF's resolvent cubic)
  formulas. Cube and square roots are replaced by arbitrary roots (`A ^ 3 = …`, `s ^ 2 = …`),
  so the statements are branch-free and cover every choice; DLMF's choice 1.11.20 of the square
  roots is a hypothesis.
* §1.11(iv): roots of `z^n = -1` and of `z^n = a + ib` (1.11.22–1.11.23).
* §1.11(v): the explicit Hurwitz determinants 1.11.25 and the Hurwitz criterion.

The depressed quartic's discriminant 1.11.17 uses TauCeti's `TauCeti.discr_resolventCubic`
(the quartic and TauCeti's resolvent cubic have the same discriminant).
-/

@[expose] public noncomputable section

open Polynomial Complex
open scoped Real

namespace DLMF.AlgebraicAnalytic

variable {K : Type*} [Field K]

/-! ## §1.11(i) Division algorithm: Horner's scheme -/

/-- DLMF 1.11.4: `f(α) = b_0`. -/
@[dlmf 1.11.E4]
theorem hornerB_zero (f : K[X]) (α : K) : hornerB f α 0 = f.eval α := by
  simp [hornerB]

/-- The quotient coefficients are `b_{k+1}` (definition of `hornerB`). -/
theorem coeff_divByMonic_X_sub_C (f : K[X]) (α : K) (k : ℕ) :
    (f /ₘ (X - C α)).coeff k = hornerB f α (k + 1) := by
  simp [hornerB]

/-- The polynomial form of DLMF 1.11.2: `f = (X - α) q + b_0` with `q = f /ₘ (X - α)`. -/
theorem eq_X_sub_C_mul_divByMonic_add_hornerB (f : K[X]) (α : K) :
    f = (X - C α) * (f /ₘ (X - C α)) + C (hornerB f α 0) := by
  rw [hornerB_zero, ← modByMonic_X_sub_C_eq_C_eval, add_comm]
  exact (modByMonic_add_div f _).symm

/-- The quotient has degree less than `n = deg f` (it is zero when `f` is constant). -/
lemma g1d_natDegree_divByMonic_lt (f : K[X]) (α : K) (hf : 0 < f.natDegree) :
    (f /ₘ (X - C α)).natDegree < f.natDegree := by
  rw [natDegree_divByMonic f (monic_X_sub_C α), natDegree_X_sub_C]
  omega

/-- The quotient of a constant polynomial by `X - α` vanishes. -/
lemma g1d_divByMonic_eq_zero (f : K[X]) (α : K) (hf : f.natDegree = 0) :
    f /ₘ (X - C α) = 0 := by
  rw [divByMonic_eq_zero_iff (monic_X_sub_C α), degree_X_sub_C]
  exact lt_of_le_of_lt (natDegree_eq_zero_iff_degree_le_zero.mp hf) (by norm_num)

/-- DLMF 1.11.2: `f(z) = (z - α)(b_n z^{n-1} + b_{n-1} z^{n-2} + ⋯ + b_1) + b_0`, where
`n = deg f`. -/
@[dlmf 1.11.E2]
theorem eval_eq_horner (f : K[X]) (α z : K) :
    f.eval z = (z - α) * ∑ k ∈ Finset.range f.natDegree, hornerB f α (k + 1) * z ^ k +
      hornerB f α 0 := by
  conv_lhs => rw [eq_X_sub_C_mul_divByMonic_add_hornerB f α]
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · simp [g1d_divByMonic_eq_zero f α h0, h0]
  · rw [eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_C,
      eval_eq_sum_range' (g1d_natDegree_divByMonic_lt f α hpos)]
    simp [coeff_divByMonic_X_sub_C]

/-- DLMF 1.11.3: the recurrence `b_k = α b_{k+1} + a_k` of Horner's scheme. It holds for every
`k` (for `k = n` it gives `b_n = a_n`, as `b_{n+1} = 0`). -/
@[dlmf 1.11.E3]
theorem hornerB_rec (f : K[X]) (α : K) (k : ℕ) :
    hornerB f α k = α * hornerB f α (k + 1) + f.coeff k := by
  have h : f.coeff k =
      ((f /ₘ (X - C α)) * (X - C α)).coeff k + (C (hornerB f α 0)).coeff k := by
    conv_lhs => rw [eq_X_sub_C_mul_divByMonic_add_hornerB f α]
    rw [coeff_add, mul_comm]
  rw [coeff_C] at h
  rcases k with _ | k
  · have h0 : ((f /ₘ (X - C α)) * (X - C α)).coeff 0 = -((f /ₘ (X - C α)).coeff 0 * α) := by
      simp [mul_sub]
    rw [h0] at h; simp only [↓reduceIte] at h
    rw [h, ← coeff_divByMonic_X_sub_C]
    ring
  · rw [coeff_mul_X_sub_C] at h; simp only [Nat.succ_ne_zero, ↓reduceIte, add_zero] at h
    rw [h, ← coeff_divByMonic_X_sub_C, ← coeff_divByMonic_X_sub_C]
    ring

/-- `b_k = 0` for `k > n`. -/
theorem hornerB_eq_zero_of_lt (f : K[X]) (α : K) {k : ℕ} (hk : f.natDegree < k) :
    hornerB f α k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [← coeff_divByMonic_X_sub_C]
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | hpos
  · simp [g1d_divByMonic_eq_zero f α h0]
  · exact coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le (g1d_natDegree_divByMonic_lt f α hpos) (by omega))

/-- DLMF 1.11.2–1.11.3: `b_n = a_n`. -/
@[dlmf 1.11.E3]
theorem hornerB_natDegree (f : K[X]) (α : K) :
    hornerB f α f.natDegree = f.coeff f.natDegree := by
  rw [hornerB_rec, hornerB_eq_zero_of_lt f α (Nat.lt_succ_self _), mul_zero, zero_add]

/-- DLMF 1.11.5: `c_k = α c_{k+1} + b_k`, `k ≥ 1`. -/
@[dlmf 1.11.E5]
theorem hornerC_rec (f : K[X]) (α : K) {k : ℕ} (hk : 1 ≤ k) :
    hornerC f α k = α * hornerC f α (k + 1) + hornerB f α k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [hornerC, Nat.add_sub_cancel]
  rw [hornerB_rec, coeff_divByMonic_X_sub_C]

/-- DLMF 1.11.5: `c_n = a_n` (for `n = deg f ≥ 1`). -/
@[dlmf 1.11.E5]
theorem hornerC_natDegree (f : K[X]) (α : K) (hf : 0 < f.natDegree) :
    hornerC f α f.natDegree = f.coeff f.natDegree := by
  have hq : (f /ₘ (X - C α)).natDegree = f.natDegree - 1 := by
    rw [natDegree_divByMonic f (monic_X_sub_C α), natDegree_X_sub_C]
  rw [hornerC, ← hq, hornerB_natDegree, hq, coeff_divByMonic_X_sub_C,
    show f.natDegree - 1 + 1 = f.natDegree by omega, hornerB_natDegree]

/-- DLMF 1.11.6: `f'(α) = c_1`. -/
@[dlmf 1.11.E6]
theorem hornerC_one (f : K[X]) (α : K) : hornerC f α 1 = (derivative f).eval α := by
  conv_rhs => rw [eq_X_sub_C_mul_divByMonic_add_hornerB f α]
  simp [hornerC, hornerB_zero, derivative_mul]

/-! ## §1.11(ii) Elementary properties -/

/-- A real polynomial of positive degree with nonnegative leading coefficient and negative value
at `0` has a positive zero (intermediate value theorem). -/
lemma g1d_exists_pos_root {f : ℝ[X]} (hdeg : 0 < f.degree) (hlc : 0 ≤ f.leadingCoeff)
    (h0 : f.eval 0 < 0) : ∃ x, 0 < x ∧ f.IsRoot x := by
  obtain ⟨M, hM, hM0⟩ := (((tendsto_atTop_of_leadingCoeff_nonneg f hdeg hlc).eventually
    (Filter.eventually_gt_atTop 0)).and (Filter.eventually_gt_atTop 0)).exists
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hM0.le (f.continuous.continuousOn)
    (show (0 : ℝ) ∈ Set.Icc (f.eval 0) (f.eval M) from ⟨h0.le, hM.le⟩)
  refine ⟨x, lt_of_le_of_ne hx.1 ?_, hfx⟩
  rintro rfl
  exact h0.ne hfx

/-- The polynomial `f(-z)` has the same degree as `f` and leading coefficient
`(-1)^n a_n`. -/
lemma g1d_comp_neg (f : ℝ[X]) :
    (f.comp (-X)).natDegree = f.natDegree ∧
      (f.comp (-X)).leadingCoeff = (-1) ^ f.natDegree * f.leadingCoeff := by
  have h1 : (-X : ℝ[X]).natDegree = 1 := by rw [natDegree_neg, natDegree_X]
  refine ⟨by rw [natDegree_comp, h1, mul_one], ?_⟩
  rw [leadingCoeff_comp (by rw [h1]; exact one_ne_zero), leadingCoeff_neg, leadingCoeff_X,
    mul_comm]

/-- DLMF §1.11(ii): every monic real polynomial of odd degree has a real zero whose sign is
opposite to that of the constant term (a zero `x` with `x a_0 ≤ 0`, and `x a_0 < 0` when
`a_0 ≠ 0`). -/
@[dlmf 1.11.ii]
theorem exists_root_sign_of_odd {f : ℝ[X]} (hm : f.Monic) (hodd : Odd f.natDegree) :
    ∃ x, f.IsRoot x ∧ (f.coeff 0 < 0 → 0 < x) ∧ (0 < f.coeff 0 → x < 0) := by
  have hpos : 0 < f.natDegree := hodd.pos
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
  rcases lt_trichotomy (f.coeff 0) 0 with h | h | h
  · obtain ⟨x, hx, hr⟩ := g1d_exists_pos_root hdeg (by rw [hm.leadingCoeff]; norm_num)
      (by rwa [← coeff_zero_eq_eval_zero])
    exact ⟨x, hr, fun _ => hx, fun h' => absurd h' (not_lt.mpr h.le)⟩
  · exact ⟨0, by rwa [IsRoot, ← coeff_zero_eq_eval_zero], fun h' => absurd h (ne_of_lt h'),
      fun h' => absurd h (ne_of_gt h')⟩
  · obtain ⟨hn, hl⟩ := g1d_comp_neg f
    obtain ⟨x, hx, hr⟩ := g1d_exists_pos_root (f := -(f.comp (-X)))
      (by rw [degree_neg]; exact natDegree_pos_iff_degree_pos.mp (hn ▸ hpos))
      (by rw [leadingCoeff_neg, hl, hm.leadingCoeff, hodd.neg_one_pow]; norm_num)
      (by simp [← coeff_zero_eq_eval_zero, h])
    refine ⟨-x, ?_, fun h' => absurd h' (not_lt.mpr h.le), fun _ => by linarith⟩
    simpa [IsRoot] using hr

/-- DLMF §1.11(ii): a monic real polynomial of even degree with negative constant term has a
positive and a negative zero. -/
@[dlmf 1.11.ii]
theorem exists_pos_neg_root_of_even {f : ℝ[X]} (hm : f.Monic) (heven : Even f.natDegree)
    (h0 : f.coeff 0 < 0) : ∃ x y, f.IsRoot x ∧ f.IsRoot y ∧ 0 < x ∧ y < 0 := by
  have hpos : 0 < f.natDegree := by
    rcases Nat.eq_zero_or_pos f.natDegree with h | h
    · have : f = 1 := by
        rw [hm.as_sum, h]; simp
      rw [this, coeff_one_zero] at h0; norm_num at h0
    · exact h
  have hdeg : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hpos
  obtain ⟨x, hx, hr⟩ := g1d_exists_pos_root hdeg (by rw [hm.leadingCoeff]; norm_num)
    (by rwa [← coeff_zero_eq_eval_zero])
  obtain ⟨hn, hl⟩ := g1d_comp_neg f
  obtain ⟨y, hy, hr'⟩ := g1d_exists_pos_root (f := f.comp (-X))
    (natDegree_pos_iff_degree_pos.mp (hn ▸ hpos))
    (by rw [hl, hm.leadingCoeff, heven.neg_one_pow]; norm_num)
    (by simpa [← coeff_zero_eq_eval_zero] using h0)
  exact ⟨x, -y, hr, by simpa [IsRoot] using hr', hx, by linarith⟩

/-- DLMF §1.11(ii), **Descartes' rule of signs**, parity part: the number of positive zeros
(with multiplicity) of a nonzero real polynomial and the number of sign changes of its
coefficients have the same parity. (The inequality is Mathlib's
`Polynomial.roots_countP_pos_le_signVariations`.) -/
@[dlmf 1.11.ii]
theorem signVariations_sub_countP_pos_even {f : ℝ[X]} (hf : f ≠ 0) :
    Even (f.signVariations - f.roots.countP (0 < ·)) := by
  sorry

/-- DLMF §1.11(ii), Descartes' rule of signs for negative zeros: the number of negative zeros of
`f` does not exceed the number of sign changes of the coefficients of `f(-z)`. -/
@[dlmf 1.11.ii]
theorem roots_countP_neg_le_signVariations (f : ℝ[X]) :
    f.roots.countP (· < 0) ≤ (f.comp (-X)).signVariations := by
  have h := roots_countP_pos_le_signVariations (f.comp (-X))
  rw [roots_comp_neg_X, Multiset.countP_map] at h
  simpa [Multiset.countP_eq_card_filter, neg_pos] using h

/-- DLMF §1.11(ii): the zeros of `z^n f(1/z)` (Mathlib's `Polynomial.reverse`) are the
reciprocals of the (nonzero) zeros of `f`. -/
@[dlmf 1.11.ii]
theorem isRoot_reverse_inv_iff (f : K[X]) {x : K} (hx : x ≠ 0) :
    f.reverse.IsRoot x⁻¹ ↔ f.IsRoot x := by
  let _ : Invertible x := invertibleOfNonzero hx
  have h := eval₂_reverse_eq_zero_iff (RingHom.id K) x f
  rw [eval₂_id, eval₂_id, invOf_eq_inv] at h
  exact h

/-- DLMF 1.11.9: the discriminant of `f = a_n ∏ (z - z_j)` is
`D = a_n^{2n-2} ∏_{j<k} (z_j - z_k)²` (Mathlib's `Polynomial.discr`; the cases `n = 2, 3` are
Mathlib's `Polynomial.discr_of_degree_eq_two` and `Cubic.discr_eq_prod_three_roots`). -/
@[dlmf 1.11.E9]
theorem discr_eq_prod_roots {n : ℕ} (a : K) (ha : a ≠ 0) (z : Fin n → K) :
    (C a * ∏ j, (X - C (z j))).discr =
      a ^ (2 * n - 2) * ∏ j, ∏ k with j < k, (z j - z k) ^ 2 := by
  sorry

/-! ## §1.11(iii) Polynomials of degrees two, three and four -/

/-- DLMF §1.11(iii): the sum and the product of the roots `(-b ± √D)/(2a)` of `az² + bz + c`
(1.11.11; the root formula itself is Mathlib's `quadratic_eq_zero_iff`) are `-b/a` and `c/a`.
Here `s` is any square root of the discriminant `D = b² - 4ac`. -/
@[dlmf 1.11.E11]
theorem quadratic_roots_sum_prod {a b c s : K} (ha : a ≠ 0) (h2 : (2 : K) ≠ 0)
    (hs : discrim a b c = s * s) :
    (-b + s) / (2 * a) + (-b - s) / (2 * a) = -b / a ∧
      (-b + s) / (2 * a) * ((-b - s) / (2 * a)) = c / a := by
  unfold discrim at hs
  constructor
  · field_simp
    ring
  · field_simp
    linear_combination hs


/-- DLMF §1.11(iii): the substitution `z = w - a/3` reduces `z³ + az² + bz + c` to
`w³ + pw + q` with `p = (3b - a²)/3`, `q = (2a³ - 9ab + 27c)/27`; so the roots of `f` are those
of `g` shifted by `-a/3`. -/
@[dlmf 1.11.iii]
theorem cubic_comp_X_sub_C {R : Type*} [Field R] [CharZero R] (a b c : R) :
    (X ^ 3 + C a * X ^ 2 + C b * X + C c).comp (X - C (a / 3)) =
      X ^ 3 + C ((3 * b - a ^ 2) / 3) * X + C ((2 * a ^ 3 - 9 * a * b + 27 * c) / 27) := by
  obtain ⟨t, rfl⟩ : ∃ t, a = 3 * t := ⟨a / 3, by field_simp⟩
  rw [show 3 * t / 3 = t by field_simp, show (3 * b - (3 * t) ^ 2) / 3 = b - 3 * t ^ 2 by
    field_simp, show (2 * (3 * t) ^ 3 - 9 * (3 * t) * b + 27 * c) / 27 =
      2 * t ^ 3 - b * t + c by field_simp; ring]
  simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp, map_sub, map_add, map_mul, map_pow,
    map_ofNat, ofNat_comp]
  ring

/-- DLMF 1.11.12: the discriminant of `w³ + pw + q` is `D = -4p³ - 27q²`. -/
@[dlmf 1.11.E12]
theorem discr_reduced_cubic {R : Type*} [CommRing R] [Nontrivial R] (p q : R) :
    (X ^ 3 + C p * X + C q : R[X]).discr = -4 * p ^ 3 - 27 * q ^ 2 := by
  have hdeg : (X ^ 3 + C p * X + C q : R[X]).degree = 3 := by
    compute_degree!
  rw [discr_of_degree_eq_three hdeg]
  have h3 : (X ^ 3 + C p * X + C q : R[X]).coeff 3 = 1 := by
    simp
  have h2 : (X ^ 3 + C p * X + C q : R[X]).coeff 2 = 0 := by
    simp
  have h1 : (X ^ 3 + C p * X + C q : R[X]).coeff 1 = p := by
    simp
  have h0 : (X ^ 3 + C p * X + C q : R[X]).coeff 0 = q := by
    simp
  rw [h3, h2, h1, h0]
  ring

/-- DLMF 1.11.13–1.11.14, **Cardano's formula**: let `s` be a square root of `-3D`, `A` a cube
root of `-27q/2 + 3s/2` with `A ≠ 0`, `B = -3p/A`, and `ρ` a primitive cube root of unity
(`ρ² + ρ + 1 = 0`). Then the roots of `w³ + pw + q` are `(A + B)/3`, `(ρA + ρ²B)/3`,
`(ρ²A + ρB)/3`. (Branch-free: every choice of the roots is covered. `A ≠ 0` fails only when
`p = 0` and `s = 9q`; then the other square root must be taken.) -/
@[dlmf 1.11.E13, dlmf 1.11.E14]
theorem cardano {p q s A ρ : ℂ} (hs : s ^ 2 = -3 * (-4 * p ^ 3 - 27 * q ^ 2))
    (hA3 : A ^ 3 = -27 / 2 * q + 3 / 2 * s) (hA : A ≠ 0) (hρ : ρ ^ 2 + ρ + 1 = 0) :
    (X ^ 3 + C p * X + C q : ℂ[X]) =
      (X - C ((A + -3 * p / A) / 3)) * (X - C ((ρ * A + ρ ^ 2 * (-3 * p / A)) / 3)) *
        (X - C ((ρ ^ 2 * A + ρ * (-3 * p / A)) / 3)) := by
  set B := -3 * p / A with hB
  have h1 : 3 * p = -(A * B) := by rw [hB]; field_simp
  have h6 : A ^ 6 + 27 * q * A ^ 3 - 27 * p ^ 3 = 0 := by
    linear_combination (A ^ 3 + (-27 / 2 * q + 3 / 2 * s) + 27 * q) * hA3 + 9 / 4 * hs
  have h2 : 27 * q = -(A ^ 3 + B ^ 3) := by
    have hA3' : A ^ 3 ≠ 0 := pow_ne_zero 3 hA
    have hB3 : B ^ 3 * A ^ 3 = -27 * p ^ 3 := by
      rw [← mul_pow]; linear_combination (A ^ 2 * B ^ 2 - 3 * p * A * B + 9 * p ^ 2) * h1
    have : (27 * q + (A ^ 3 + B ^ 3)) * A ^ 3 = 0 := by linear_combination h6 + hB3
    linear_combination (mul_eq_zero.mp this).resolve_right hA3'
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub]
  linear_combination (-A - B + 3 * x) * (-A ^ 2 * ρ + A ^ 2 - A * B * ρ ^ 2 + A * B * ρ -
    A * B - B ^ 2 * ρ + B ^ 2 + 3 * A * x + 3 * B * x) / 27 * hρ + x / 3 * h1 + 1 / 27 * h2

/-- DLMF 1.11.15: `ρ = -1/2 + (1/2)√-3 = e^{2πi/3}` and `ρ² = e^{-2πi/3}` (with the principal
square root `√-3 = i√3`), and `ρ² + ρ + 1 = 0`. -/
@[dlmf 1.11.E15]
theorem cardano_rho :
    exp (2 * π * I / 3) = -1 / 2 + 1 / 2 * (I * Real.sqrt 3) ∧
      exp (2 * π * I / 3) ^ 2 = exp (-2 * π * I / 3) ∧
      exp (2 * π * I / 3) ^ 2 + exp (2 * π * I / 3) + 1 = 0 := by
  have hc : Real.cos (2 * π / 3) = -1 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have hs : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have h1 : exp (2 * π * I / 3) = -1 / 2 + 1 / 2 * (I * Real.sqrt 3) := by
    rw [show (2 * π * I / 3 : ℂ) = ((2 * π / 3 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
      ← ofReal_cos, ← ofReal_sin, hc, hs]
    push_cast; ring
  refine ⟨h1, ?_, ?_⟩
  · rw [← exp_nat_mul, show ((2 : ℕ) : ℂ) * (2 * π * I / 3) = -2 * π * I / 3 + 2 * π * I by
      push_cast; ring, exp_add, exp_two_pi_mul_I, mul_one]
  · rw [h1]
    have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
      rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    linear_combination (1 / 4 * I ^ 2) * h3 + 3 / 4 * I_sq

/-- DLMF 1.11.16: the substitution `z = w - a/4` reduces `z⁴ + az³ + bz² + cz + d` to
`w⁴ + pw² + qw + r` with `p = (-3a² + 8b)/8`, `q = (a³ - 4ab + 8c)/8`,
`r = (-3a⁴ + 16a²b - 64ac + 256d)/256`. -/
@[dlmf 1.11.E16]
theorem quartic_comp_X_sub_C {R : Type*} [Field R] [CharZero R] (a b c d : R) :
    (X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d).comp (X - C (a / 4)) =
      X ^ 4 + C ((-3 * a ^ 2 + 8 * b) / 8) * X ^ 2 + C ((a ^ 3 - 4 * a * b + 8 * c) / 8) * X +
        C ((-3 * a ^ 4 + 16 * a ^ 2 * b - 64 * a * c + 256 * d) / 256) := by
  obtain ⟨t, rfl⟩ : ∃ t, a = 4 * t := ⟨a / 4, by field_simp⟩
  rw [show 4 * t / 4 = t by field_simp, show (-3 * (4 * t) ^ 2 + 8 * b) / 8 = b - 6 * t ^ 2 by
    field_simp; ring, show ((4 * t) ^ 3 - 4 * (4 * t) * b + 8 * c) / 8 = 8 * t ^ 3 - 2 * b * t + c
    by field_simp; ring, show (-3 * (4 * t) ^ 4 + 16 * (4 * t) ^ 2 * b - 64 * (4 * t) * c +
      256 * d) / 256 = -3 * t ^ 4 + b * t ^ 2 - c * t + d by field_simp; ring]
  simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp, map_sub, map_add, map_mul, map_pow,
    map_ofNat, map_neg, ofNat_comp]
  ring

/-- DLMF 1.11.17: the discriminant of `w⁴ + pw² + qw + r` is
`16p⁴r - 4p³q² - 128p²r² + 144pq²r - 27q⁴ + 256r³`. -/
@[dlmf 1.11.E17]
theorem discr_reduced_quartic {R : Type*} [CommRing R] [Nontrivial R] (p q r : R) :
    (X ^ 4 + C p * X ^ 2 + C q * X + C r : R[X]).discr =
      16 * p ^ 4 * r - 4 * p ^ 3 * q ^ 2 - 128 * p ^ 2 * r ^ 2 + 144 * p * q ^ 2 * r -
        27 * q ^ 4 + 256 * r ^ 3 := by
  rw [TauCeti.discr_resolventCubic, TauCeti.resolventCubic_def]
  have hdeg : (X ^ 3 - C p * X ^ 2 - C (4 * r) * X + C (4 * p * r - q ^ 2) : R[X]).degree = 3 := by
    compute_degree!
  rw [discr_of_degree_eq_three hdeg]
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  norm_num
  ring

/-- DLMF 1.11.18–1.11.20, **Ferrari's method**: let `θ₁, θ₂, θ₃` be the roots of the resolvent
cubic `z³ - 2pz² + (p² - 4r)z + q²` and `s_j` square roots of `-θ_j` chosen with
`s₁ s₂ s₃ = -q` (1.11.20). Then the roots of `w⁴ + pw² + qw + r` are
`α₁ = (s₁ + s₂ + s₃)/2`, `α₂ = (s₁ - s₂ - s₃)/2`, `α₃ = (-s₁ + s₂ - s₃)/2`,
`α₄ = (-s₁ - s₂ + s₃)/2` (1.11.19). -/
@[dlmf 1.11.E18, dlmf 1.11.E19, dlmf 1.11.E20]
theorem ferrari {p q r θ₁ θ₂ θ₃ s₁ s₂ s₃ : ℂ}
    (hθ : (dlmfResolventCubic p q r).roots = {θ₁, θ₂, θ₃})
    (hs₁ : s₁ ^ 2 = -θ₁) (hs₂ : s₂ ^ 2 = -θ₂) (hs₃ : s₃ ^ 2 = -θ₃) (hq : s₁ * s₂ * s₃ = -q) :
    (X ^ 4 + C p * X ^ 2 + C q * X + C r : ℂ[X]) =
      (X - C ((s₁ + s₂ + s₃) / 2)) * (X - C ((s₁ - s₂ - s₃) / 2)) *
        (X - C ((-s₁ + s₂ - s₃) / 2)) * (X - C ((-s₁ - s₂ + s₃) / 2)) := by
  have hb := Cubic.b_eq_three_roots (φ := RingHom.id ℂ) (P := dlmfResolventCubic p q r)
    one_ne_zero hθ
  have hc := Cubic.c_eq_three_roots (φ := RingHom.id ℂ) (P := dlmfResolventCubic p q r)
    one_ne_zero hθ
  simp only [dlmfResolventCubic, RingHom.id_apply, one_mul] at hb hc
  have hG0 : s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2 + 2 * p = 0 := by
    linear_combination hs₁ + hs₂ + hs₃ - hb
  have hG1 : s₁ ^ 2 * s₂ ^ 2 + s₁ ^ 2 * s₃ ^ 2 + s₂ ^ 2 * s₃ ^ 2 - (p ^ 2 - 4 * r) = 0 := by
    linear_combination (-θ₂ - θ₃) * hs₁ + (s₁ ^ 2 - θ₃) * hs₂ + (s₁ ^ 2 + s₂ ^ 2) * hs₃ - hc
  have hG2 : s₁ * s₂ * s₃ + q = 0 := by linear_combination hq
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub]
  linear_combination (x ^ 2 / 2 - (s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2 + 2 * p - 4 * p) / 16) * hG0 +
    1 / 4 * hG1 + x * hG2


/-! ## §1.11(iv) Roots of unity and of other constants -/

/-- DLMF §1.11(iv): the roots of `z^n + 1 = 0` are `e^{πi/n}, e^{3πi/n}, …, e^{(2n-1)πi/n}`.
(The roots of unity are Mathlib's `Complex.mem_rootsOfUnity`.) -/
@[dlmf 1.11.iv]
theorem pow_eq_neg_one_iff {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    z ^ n = -1 ↔ ∃ k < n, z = exp ((2 * k + 1) * π * I / n) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have _ : NeZero n := ⟨hn⟩
  have hω : exp (π * I / n) ^ n = -1 := by
    rw [← exp_nat_mul, show (n : ℂ) * (π * I / n) = π * I by field_simp, exp_pi_mul_I]
  constructor
  · intro h
    have hy : (z * exp (-(π * I / n))) ^ n = 1 := by
      rw [mul_pow, h, exp_neg, inv_pow, hω]; norm_num
    obtain ⟨i, hi, hy'⟩ := (isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one hy
    refine ⟨i, hi, ?_⟩
    have : z = exp (2 * π * I / n) ^ i * exp (π * I / n) := by
      rw [hy', mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
    rw [this, ← exp_nat_mul, ← exp_add]
    congr 1
    field_simp
  · rintro ⟨k, -, rfl⟩
    rw [← exp_nat_mul, show (n : ℂ) * ((2 * k + 1) * π * I / n) = k * (2 * π * I) + π * I by
      field_simp, exp_add, exp_nat_mul_two_pi_mul_I, exp_pi_mul_I, one_mul]

/-- DLMF 1.11.22–1.11.23: for `n ≥ 1` and real `a`, `b`, the roots of `z^n = a + ib` are
`R^{1/n}(cos((α + 2kπ)/n) + i sin((α + 2kπ)/n))`, `k = 0, …, n-1`, with
`R = (a² + b²)^{1/2}` and `α = ph(a + ib)` the principal phase. (For `a + ib = 0` all these
values are `0`.) -/
@[dlmf 1.11.E22, dlmf 1.11.E23]
theorem pow_eq_iff {n : ℕ} (hn : n ≠ 0) (a b : ℝ) (z : ℂ) :
    z ^ n = a + b * I ↔ ∃ k < n,
      z = ((Real.sqrt (a ^ 2 + b ^ 2)) ^ (1 / n : ℝ) : ℝ) *
        (Real.cos ((arg (a + b * I) + 2 * k * π) / n) +
          Real.sin ((arg (a + b * I) + 2 * k * π) / n) * I) := by
  have hcs : ∀ x : ℝ, ((Real.cos x : ℝ) : ℂ) + (Real.sin x : ℝ) * I = exp (x * I) := by
    intro x; rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  have hR : Real.sqrt (a ^ 2 + b ^ 2) = ‖(a + b * I : ℂ)‖ := (norm_add_mul_I a b).symm
  simp_rw [hcs, hR]
  set c : ℂ := a + b * I with hc
  set r : ℝ := ‖c‖ ^ (1 / n : ℝ) with hr
  have hrn : (r : ℂ) ^ n = ‖c‖ := by
    rw [← ofReal_pow, hr, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hn]
  have hwn : ∀ k : ℕ, ((r : ℂ) * exp ((((arg c + 2 * k * π) / n : ℝ) : ℂ) * I)) ^ n = c := by
    intro k
    rw [mul_pow, hrn, ← exp_nat_mul, show (n : ℂ) * ((((arg c + 2 * k * π) / n : ℝ) : ℂ) * I) =
      arg c * I + k * (2 * π * I) by push_cast; field_simp, exp_add,
      exp_nat_mul_two_pi_mul_I, mul_one, norm_mul_exp_arg_mul_I]
  have _ : NeZero n := ⟨hn⟩
  constructor
  · intro h
    by_cases hc0 : c = 0
    · refine ⟨0, Nat.pos_of_ne_zero hn, ?_⟩
      have hz : z = 0 := (pow_eq_zero_iff hn).mp (h.trans hc0)
      rw [hz, hr, hc0, norm_zero, Real.zero_rpow (by positivity)]
      simp
    · set w0 := (r : ℂ) * exp ((((arg c + 2 * ((0 : ℕ) : ℝ) * π) / n : ℝ) : ℂ) * I) with hw0d
      have hr0 : 0 < r := Real.rpow_pos_of_pos (norm_pos_iff.mpr hc0) _
      have hw0 : w0 ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hr0.ne') (exp_ne_zero _)
      have hy : (z / w0) ^ n = 1 := by rw [div_pow, h, hwn 0, div_self hc0]
      obtain ⟨i, hi, hy'⟩ := (isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one hy
      refine ⟨i, hi, ?_⟩
      have hz : z = w0 * exp (2 * π * I / n) ^ i := by rw [hy', mul_div_cancel₀ _ hw0]
      rw [hz, hw0d, mul_assoc, ← exp_nat_mul, ← exp_add]
      congr 2
      push_cast
      field_simp
      ring
  · rintro ⟨k, -, rfl⟩
    exact hwn k


/-! ## §1.11(v) Stable polynomials -/

/-- DLMF 1.11.25: `D₁ = a₁`. -/
@[dlmf 1.11.E25]
theorem hurwitzDet_one (f : ℝ[X]) : hurwitzDet f 1 = f.coeff 1 := by
  simp [hurwitzDet, hurwitzMatrix, coeffInt]

/-- DLMF 1.11.25: `D₂ = a₁a₂ - a₃a₀`. -/
@[dlmf 1.11.E25]
theorem hurwitzDet_two (f : ℝ[X]) :
    hurwitzDet f 2 = f.coeff 1 * f.coeff 2 - f.coeff 3 * f.coeff 0 := by
  simp [hurwitzDet, hurwitzMatrix, coeffInt, Matrix.det_fin_two]

/-- DLMF 1.11.25: `D₃ = det [[a₁, a₃, a₅], [a₀, a₂, a₄], [0, a₁, a₃]]`. -/
@[dlmf 1.11.E25]
theorem hurwitzDet_three (f : ℝ[X]) :
    hurwitzDet f 3 = Matrix.det !![f.coeff 1, f.coeff 3, f.coeff 5; f.coeff 0, f.coeff 2,
      f.coeff 4; 0, f.coeff 1, f.coeff 3] := by
  simp [hurwitzDet, hurwitzMatrix, coeffInt, Matrix.det_fin_three]


/-- DLMF §1.11(v), **Hurwitz criterion**: a real polynomial `f` of degree `n` (`a_n ≠ 0`) is
stable iff `a₀ ≠ 0`, `D_{2k} > 0` for `k = 1, …, ⌊n/2⌋` (that is, `2k ≤ n`), and
`sign D_{2k+1} = sign a₀` for `k = 0, 1, …, ⌊(n-1)/2⌋` (that is, `2k + 1 ≤ n`; the range is empty
for `n = 0`). (Checked numerically on random polynomials of degrees 1–7.) -/
@[dlmf 1.11.v]
theorem isStablePolynomial_iff_hurwitz {f : ℝ[X]} (hf : f ≠ 0) :
    IsStablePolynomial f ↔ f.coeff 0 ≠ 0 ∧
      (∀ k, 1 ≤ k → 2 * k ≤ f.natDegree → 0 < hurwitzDet f (2 * k)) ∧
      (∀ k, 2 * k + 1 ≤ f.natDegree →
        SignType.sign (hurwitzDet f (2 * k + 1)) = SignType.sign (f.coeff 0)) := by
  sorry

end DLMF.AlgebraicAnalytic
