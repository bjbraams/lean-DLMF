/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.AskeyScheme
public import DLMF.Confluent.Recurrence
public import DLMF.OrthogonalPolynomials.BinomialSeries
public import DLMF.OrthogonalPolynomials.PollaczekMoments
import DLMF.Gamma.SpecialValues

/-!
# Hahn and Meixner polynomial identities

Definitions of the polynomials of the Hahn class (DLMF §18.20) and their weights
(DLMF §18.19), with the continuous orthogonality of the continuous Hahn and Meixner–Pollaczek
polynomials, duality, difference equations, forward differences, recurrences and generating
functions of the discrete families. Terminating hypergeometric sums carry an explicit
cutoff, which implements DLMF's convention when a lower parameter is a negative integer.

## Main definitions

* `terminatingHypergeometric`: a terminating hypergeometric sum with an explicit cutoff.
* `hahn`, `krawtchouk`, `meixner`, `charlier`: DLMF 18.20.5–18.20.8.
* `continuousHahn`, `meixnerPollaczek`: DLMF 18.20.9 and 18.20.10.
* `continuousHahnWeight`, `meixnerPollaczekWeight`: the weights DLMF 18.19.2 and 18.19.7.

## Main results

* `continuousHahn_orthogonal`, `meixnerPollaczek_orthogonality`: DLMF 18.19.4 and 18.19.9.
* `krawtchouk_duality`, `meixner_duality`, `charlier_duality`: DLMF 18.21.2.
* `hahn_difference_equation`: DLMF 18.22.10.
* `krawtchouk_difference_equation`, `meixner_difference_equation`,
  `charlier_difference_equation`: the difference equations of Table 18.22.2.
* `hahn_forward_difference`, `krawtchouk_forward_difference`, `meixner_forward_difference`,
  `charlier_forward_difference`: DLMF 18.22.19, 18.22.21, 18.22.23 and 18.22.25.
* `integral_meixnerPollaczek_mul_div_cosh`: the orthonormal half-parameter case.
* `meixnerPollaczek_recurrence`, `meixnerPollaczek_central_difference`: DLMF 18.22.8 and
  18.22.29.
* `krawtchouk_generating_function`, `meixner_generating_function`: DLMF 18.23.3 and 18.23.4.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- The forward difference of a Pochhammer symbol in a shifted argument. -/
theorem pochhammer_half_sub (w : ℂ) (k : ℕ) :
    pochhammer (w - 1 / 2) (k + 1) - pochhammer (w + 1 / 2) (k + 1) = -(k + 1) *
        pochhammer (w + 1 / 2) k := by
  rw [pochhammer_succ_left (w - 1 / 2), pochhammer_succ (w + 1 / 2), show w - 1 / 2 + 1 =
      w + 1 / 2 by ring]
  ring

/-- `e^{iφ} (1 - e^{-2iφ}) = 2 i sin φ`. -/
theorem exp_mul_one_sub_exp (phi : ℂ) :
    exp (I * phi) * (1 - exp (-2 * I * phi)) = 2 * I * sin phi := by
  have h1 : exp (I * phi) * exp (-2 * I * phi) = exp (-phi * I) := by
    rw [← exp_add]; ring_nf
  rw [Complex.sin, mul_sub, mul_one, h1, show I * phi = phi * I by ring]
  linear_combination (exp (phi * I) - exp (-phi * I)) * I_sq

/-- The Meixner–Pollaczek difference operator on the basis `(w)_{k+1}`, `w = λ + i x`. -/
theorem mp_basis_succ (lam phi w : ℂ) (n k : ℕ) :
    exp (I * phi) * (-I * (w - 2 * lam)) * (pochhammer (w - 1) (k + 1) - pochhammer w (k + 1)) +
      exp (-I * phi) * (-I * w) * (pochhammer (w + 1) (k + 1) - pochhammer w (k + 1)) +
      2 * n * sin phi * pochhammer w (k + 1) =
      2 * (n - (k + 1)) * sin phi * pochhammer w (k + 1) -
        I * (k + 1) * exp (I * phi) * (k + 2 * lam) * pochhammer w k := by
  have hS := exp_mul_one_sub_exp phi
  have h1 : exp (I * phi) * exp (-2 * I * phi) = exp (-I * phi) := by rw [← exp_add]; ring_nf
  have hsin : 2 * I * sin phi = exp (I * phi) - exp (-I * phi) := by
    rw [← hS, mul_sub, mul_one, h1]
  have hrel : pochhammer w k * (w + k) = w * pochhammer (w + 1) k := by
    rw [← pochhammer_succ, pochhammer_succ_left]
  rw [pochhammer_succ_left (w - 1), show w - 1 + 1 = w by ring, pochhammer_succ w k,
                                                            pochhammer_succ (w + 1) k]
  linear_combination (-(I) * pochhammer w k * ((k : ℂ) + 1) * (k + w)) * hsin +
    (I * exp (-I * phi) * (k + w + 1)) * hrel +
    (2 * sin phi * pochhammer w k * ((k : ℂ) + 1) * (w + k)) * I_sq

/-- The continuous Hahn difference operator on the basis `(w)_{k+1}`, `w = a + i x`. -/
theorem ch_basis_succ (a b c d w : ℂ) (n k : ℕ) :
    -((w - a - c) * (w - a - d)) * (pochhammer (w - 1) (k + 1) - pochhammer w (k + 1)) -
      w * (w - a + b) * (pochhammer (w + 1) (k + 1) - pochhammer w (k + 1)) +
      n * (n + a + b + c + d - 1) * pochhammer w (k + 1) =
      (n - (k + 1)) * (n + (k + 1) + a + b + c + d - 1) * pochhammer w (k + 1) +
        (k + 1) * (a + c + k) * (a + d + k) * pochhammer w k := by
  have hrel : pochhammer w k * (w + k) = w * pochhammer (w + 1) k := by
    rw [← pochhammer_succ, pochhammer_succ_left]
  rw [pochhammer_succ_left (w - 1), show w - 1 + 1 = w by ring, pochhammer_succ w k,
                                                            pochhammer_succ (w + 1) k]
  linear_combination (w - a + b) * (k + w + 1) * hrel

/-- The Hahn difference operator on the basis `(u)_{k+1}`, `u = -x`. -/
theorem hahn_basis_succ (α β N u : ℂ) (n k : ℕ) :
    (u - α - 1) * (u + N) * (pochhammer (u - 1) (k + 1) - pochhammer u (k + 1)) +
      u * (u + β + N + 1) * (pochhammer (u + 1) (k + 1) - pochhammer u (k + 1)) -
      n * (n + α + β + 1) * pochhammer u (k + 1) =
      (k + 1 - n) * (k + 1 + n + α + β + 1) * pochhammer u (k + 1) +
        (k + 1) * (N - k) * (α + k + 1) * pochhammer u k := by
  have hrel : pochhammer u k * (u + k) = u * pochhammer (u + 1) k := by
    rw [← pochhammer_succ, pochhammer_succ_left]
  rw [pochhammer_succ_left (u - 1), show u - 1 + 1 = u by ring, pochhammer_succ u k,
                                                            pochhammer_succ (u + 1) k]
  linear_combination (-((k + u + 1) * (N + β + u + 1))) * hrel

/-- The continuous Hahn normalization times its finite Pochhammer sum. -/
theorem continuousHahn_eq_hahnSum (a b c d : ℂ) (n : ℕ) (x : ℝ) :
    continuousHahn a b c d n x =
      (I ^ n * pochhammer (a + c) n * pochhammer (a + d) n / n.factorial) *
        HahnMoments.hahnSum a b c d n x := by
  unfold continuousHahn terminatingHypergeometric HahnMoments.hahnSum
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one_pow, mul_one]
  ring

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ, continuousHahn a b (star
a) (star b) m x * continuousHahn a b (star a) (star b) n x * continuousHahnWeight a b x = 0`. -/
@[dlmf 18.19.E4]
theorem continuousHahn_orthogonal {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {m n : ℕ}
    (hmn : m ≠ n) :
    ∫ x : ℝ, continuousHahn a b (star a) (star b) m x *
      continuousHahn a b (star a) (star b) n x * continuousHahnWeight a b x = 0 := by
  let C (k : ℕ) : ℂ := I ^ k * pochhammer (a + star a) k * pochhammer (a + star b) k / k.factorial
  have he (x : ℝ) : continuousHahn a b (star a) (star b) m x *
      continuousHahn a b (star a) (star b) n x * continuousHahnWeight a b x =
        (C m * C n) * (HahnMoments.hahnSum a b (star a) (star b) m x *
          HahnMoments.hahnSum a b (star a) (star b) n x *
              HahnMoments.weight a b (star a) (star b) x) := by
    rw [continuousHahn_eq_hahnSum, continuousHahn_eq_hahnSum]
    dsimp only [C, continuousHahnWeight, HahnMoments.weight]
    ring
  rw [integral_congr_ae (Eventually.of_forall he), integral_const_mul,
    HahnMoments.hahnSum_orthogonal ha hb (by simpa using ha) (by simpa using hb) hmn, mul_zero]

/-- The angular parameter gives the transform scale. -/
theorem pollaczek_scale_angle (phi : ℝ) : PollaczekMoments.scale (2*phi-π) = 2*sin (phi:ℂ) := by
  dsimp only [PollaczekMoments.scale]
  rw [show (2*phi-π)/2 = phi-π/2 by ring, Real.cos_sub_pi_div_two]
  push_cast
  rfl
/-- The angular phase agrees with the usual Pollaczek phase. -/
theorem pollaczek_phase_angle (phi : ℝ) : exp (I*(phi:ℂ)) = I*PollaczekMoments.phase (2*phi-π) := by
  dsimp only [PollaczekMoments.phase]
  have he : I*(phi:ℂ) = π/2*I+I*((2*phi-π:ℝ):ℂ)/2 := by
    push_cast
    ring
  rw [he, Complex.exp_add, exp_pi_div_two_mul_I]
/-- The hypergeometric argument is the scale divided by the transform phase. -/
theorem pollaczek_argument_angle (phi : ℝ) :
    1-exp (-2*I*(phi:ℂ)) = PollaczekMoments.scale (2*phi-π)/PollaczekMoments.phase (2*phi-π) := by
  let θ := 2*phi-π
  have hscale : PollaczekMoments.scale θ = exp (I*θ/2)+exp (-I*θ/2) := by
    dsimp only [PollaczekMoments.scale]
    push_cast
    rw [Complex.two_cos]
    congr 1 <;> congr 1 <;> ring
  have hphase : PollaczekMoments.phase θ ≠ 0 := Complex.exp_ne_zero _
  change 1-exp (-2*I*(phi:ℂ)) = PollaczekMoments.scale θ/PollaczekMoments.phase θ
  apply (eq_div_iff hphase).mpr
  rw [hscale]
  dsimp only [PollaczekMoments.phase]
  have he : exp (-2*I*(phi:ℂ))*exp (I*θ/2) = -exp (-I*θ/2) := by
    rw [← Complex.exp_add, ← neg_one_mul (exp (-I*θ/2)), ← exp_neg_pi_mul_I, ← Complex.exp_add]
    congr 1
    dsimp only [θ]
    push_cast
    ring
  rw [sub_mul, one_mul, he]
  ring
/-- The standard terminating definition equals the transform-adapted finite sum. -/
theorem meixnerPollaczek_eq_poly (lam phi : ℝ) (n : ℕ) (x : ℝ) :
    meixnerPollaczek lam phi n x =
      (pochhammer (2*(lam:ℂ)) n/n.factorial*(I*PollaczekMoments.phase (2*phi-π))^n)*
        PollaczekMoments.poly lam (2*phi-π) n x := by
  have he : exp (I*(n:ℂ)*(phi:ℂ)) = (I*PollaczekMoments.phase (2*phi-π))^n := by
    rw [← pollaczek_phase_angle, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [meixnerPollaczek, he, pollaczek_argument_angle]
  congr 1
  unfold terminatingHypergeometric PollaczekMoments.poly
  apply Finset.sum_congr rfl
  intro k hk
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [pochhammer_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hf : (k.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp

/-- Identity under the stated parameter and domain assumptions: `∫ x : ℝ, meixnerPollaczek lam phi
m x * meixnerPollaczek lam phi n x * meixnerPollaczekWeight lam phi x = if m = n then 2 *
Real.pi * Gamma (n + 2 * (lam : ℂ)) / ((2 * sin (phi : ℂ)) ^ (2 * (lam : ℂ)) * n.factorial)
else 0`. -/
@[dlmf 18.19.E9]
theorem meixnerPollaczek_orthogonality {lam phi : ℝ} (hlam : 0 < lam) (hphi : 0 < phi)
    (hphiπ : phi < Real.pi) (m n : ℕ) :
    ∫ x : ℝ, meixnerPollaczek lam phi m x * meixnerPollaczek lam phi n x *
      meixnerPollaczekWeight lam phi x =
      if m = n then 2 * Real.pi * Gamma (n + 2 * (lam : ℂ)) /
        ((2 * sin (phi : ℂ)) ^ (2 * (lam : ℂ)) * n.factorial) else 0 := by
  have hθ : |2*phi-π| < π := by rw [abs_lt]; constructor <;> linarith
  let C (k : ℕ) : ℂ := pochhammer (2*(lam:ℂ)) k/k.factorial*(I*PollaczekMoments.phase (2*phi-π))^k
  have he (x : ℝ) : meixnerPollaczek lam phi m x*meixnerPollaczek lam phi n x*
      meixnerPollaczekWeight lam phi x = (C m*C n)*
      (PollaczekMoments.poly lam (2*phi-π) m x*PollaczekMoments.poly lam (2*phi-π) n x*
        PollaczekMoments.weight lam (2*phi-π) x) := by
    rw [meixnerPollaczek_eq_poly, meixnerPollaczek_eq_poly]
    dsimp only [C, meixnerPollaczekWeight, PollaczekMoments.weight]
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall he), integral_const_mul]
  by_cases hmn : m = n
  · subst m
    rw [ite_eq_left rfl, ← pow_two]
    change (pochhammer (2*(lam:ℂ)) n/n.factorial*(I*PollaczekMoments.phase (2*phi-π))^n)^2 * _ = _
    rw [PollaczekMoments.normalized_square hlam hθ, pollaczek_scale_angle, add_comm (n:ℂ)]
  · rw [ite_eq_right hmn, PollaczekMoments.poly_orthogonal hlam hθ hmn, mul_zero]

/-- Meixner–Pollaczek polynomials with `λ = 1/2` and `φ = π/2` are orthonormal
for the hyperbolic secant density on the real line. -/
lemma integral_meixnerPollaczek_mul_div_cosh (m n : ℕ) :
    (∫ x : ℝ, meixnerPollaczek (1 / 2) (Real.pi / 2) m x *
      meixnerPollaczek (1 / 2) (Real.pi / 2) n x /
        (Real.cosh (Real.pi * x) : ℂ)) = if m = n then 1 else 0 := by
  have meixnerPollaczekWeight_half_pi_div_two (x : ℝ) :
      meixnerPollaczekWeight (1 / 2) (Real.pi / 2) x =
        (Real.pi : ℂ) / (Real.cosh (Real.pi * x) : ℂ) := by
    rw [meixnerPollaczekWeight,
      show (2 : ℂ) * (Real.pi / 2) - Real.pi = 0 by ring, zero_mul, exp_zero, mul_one]
    exact (DLMF.Gamma.Gamma_half_add_mul_I x).1.trans
      (by exact_mod_cast (DLMF.Gamma.Gamma_half_add_mul_I x).2)
  have h := meixnerPollaczek_orthogonality
    (lam := (1 / 2 : ℝ)) (phi := Real.pi/2) (by norm_num) (by positivity)
    (by linarith [Real.pi_pos]) m n
  have he (x : ℝ) : meixnerPollaczek (1 / 2) (Real.pi / 2) m x *
      meixnerPollaczek (1 / 2) (Real.pi / 2) n x *
        meixnerPollaczekWeight (1 / 2) (Real.pi / 2) x =
      (Real.pi : ℂ) * (meixnerPollaczek (1 / 2) (Real.pi / 2) m x *
        meixnerPollaczek (1 / 2) (Real.pi / 2) n x /
          (Real.cosh (Real.pi * x) : ℂ)) := by
    rw [meixnerPollaczekWeight_half_pi_div_two]
    ring
  simp only [ofReal_div, ofReal_one, ofReal_ofNat] at h
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const_mul] at h
  norm_num only [show (2 : ℂ) * (1 / 2)=1 by norm_num, sin_pi_div_two, cpow_one,
    Gamma_nat_eq_factorial] at h
  have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hmn : m = n
  · rw [ite_eq_left hmn] at h ⊢
    have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp [hn, hp] at h
    exact h
  · rw [ite_eq_right hmn] at h ⊢
    exact (mul_eq_zero.mp h).resolve_left hp


/-- A two-numerator terminating sum is a terminating Gauss series. -/
theorem terminatingHypergeometric_eq_ordinaryHypergeometric (n : ℕ) (b c z : ℂ) :
    terminatingHypergeometric n [-(n : ℂ), b] [c] z = ₂F₁ (-(n : ℂ)) b c z := by
  rw [ordinaryHypergeometric_eq_sum_neg_nat]
  unfold terminatingHypergeometric gaussHypergeometricCoeff
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

/-- A second terminating upper parameter permits extending the cutoff to the larger index. -/
theorem terminatingHypergeometric_two_neg_nat (n m : ℕ) (b : List ℂ) (z : ℂ) :
    terminatingHypergeometric n [-(n : ℂ), -(m : ℂ)] b z =
      ∑ k ∈ Finset.range (max n m + 1), pochhammer (-(n : ℂ)) k * pochhammer (-(m : ℂ)) k /
        (b.map (fun t => pochhammer t k)).prod * z ^ k / (k.factorial : ℂ) := by
  simp only [terminatingHypergeometric, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (le_max_left n m) 1))
  intro k _ hk
  have hnk : n < k := by
    rw [Finset.mem_range] at hk
    omega
  simp [pochhammer_neg_nat_eq_zero hnk]

/-- Symmetry remains valid even when a lower parameter is a nonpositive integer. -/
theorem terminatingHypergeometric_two_neg_nat_swap (n m : ℕ) (b : List ℂ) (z : ℂ) :
    terminatingHypergeometric n [-(n : ℂ), -(m : ℂ)] b z =
      terminatingHypergeometric m [-(m : ℂ), -(n : ℂ)] b z := by
  rw [terminatingHypergeometric_two_neg_nat, terminatingHypergeometric_two_neg_nat,
      Nat.max_comm m n]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (pochhammer (-(n : ℂ)) k)]

/-- Identity under the stated parameter and domain assumptions: `krawtchouk p N n x = krawtchouk p
N x n`. -/
@[dlmf 18.21.E2]
theorem krawtchouk_duality (p : ℂ) {N n x : ℕ} :
    krawtchouk p N n x = krawtchouk p N x n := by
  exact terminatingHypergeometric_two_neg_nat_swap n x _ _

/-- Identity under the stated parameter and domain assumptions: `meixner β c n x = meixner β c x
n`. -/
@[dlmf 18.21.E2]
theorem meixner_duality (β c : ℂ) (n x : ℕ) : meixner β c n x = meixner β c x n := by
  exact terminatingHypergeometric_two_neg_nat_swap n x _ _

/-- Identity under the stated parameter and domain assumptions: `charlier a n x = charlier a x n`.
-/
@[dlmf 18.21.E2]
theorem charlier_duality (a : ℂ) (n x : ℕ) : charlier a n x = charlier a x n := by
  exact terminatingHypergeometric_two_neg_nat_swap n x _ _

/-- Identity under the stated parameter and domain assumptions: `(x + α + 1) * (x - N) * (hahn α β
N n (x + 1) - hahn α β N n x) + x * (x - β - N - 1) * (hahn α β N n (x - 1) - hahn α β N n x)
= n * (n + α + β + 1) * hahn α β N n x`. -/
@[dlmf 18.22.E10]
theorem hahn_difference_equation {α β : ℂ} (hα : -1 < α.re) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    (x + α + 1) * (x - N) * (hahn α β N n (x + 1) - hahn α β N n x) +
      x * (x - β - N - 1) * (hahn α β N n (x - 1) - hahn α β N n x) =
      n * (n + α + β + 1) * hahn α β N n x := by
  have hpA : ∀ k : ℕ, pochhammer (α + 1) k ≠ 0 := fun k =>
    pochhammer_ne_zero_of_re_pos (by simp; linarith) k
  have hAk : ∀ k : ℕ, α + 1 + k ≠ 0 := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hpN : ∀ k : ℕ, k ≤ N → pochhammer (-(N : ℂ)) k ≠ 0 := fun k hk => by
    rw [pochhammer_neg_coe_nat]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hk).ne')
  set s : ℂ := (n : ℂ) + α + β + 1 with hs
  set u : ℂ := -x with hu
  set cf : ℕ → ℂ := fun k => pochhammer (-(n : ℂ)) k * pochhammer s k /
      (pochhammer (α + 1) k * pochhammer (-(N : ℂ)) k) /
    k ! with hcf
  set G : ℕ → ℂ := fun k => cf k * ((k - n) * (k + n + α + β + 1) * pochhammer u k) with hG
  set B : ℕ → ℂ := fun k => (u - α - 1) * (u + N) * (pochhammer (u - 1) k - pochhammer u k) +
      u * (u + β + N + 1) * (pochhammer (u + 1) k - pochhammer u k) - n * (n + α + β + 1) *
          pochhammer u k with hB
  have hrec : ∀ k : ℕ, k < n → cf (k + 1) * ((k + 1) * (N - k) * (α + k + 1)) =
      -(cf k * ((k - n) * (s + k))) := by
    intro k hk
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
    have hNk : -(N : ℂ) + k ≠ 0 := fun h => by
      have : (k : ℂ) = N := by linear_combination h
      exact absurd (by exact_mod_cast this : k = N) (by omega)
    have := hpA k; have := hAk k; have := hpN k (by omega)
    simp only [hcf]
    rw [pochhammer_succ, pochhammer_succ s, pochhammer_succ (α + 1), pochhammer_succ (-(N : ℂ)),
        Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have htel : ∀ k : ℕ, k < n → cf (k + 1) * B (k + 1) = G (k + 1) - G k := by
    intro k hk
    simp only [hB, hG]
    rw [hahn_basis_succ α β N u n k]
    have hr := hrec k hk
    push_cast
    linear_combination (pochhammer u k) * hr
  have hkey : ∑ k ∈ Finset.range (n + 1), cf k * B k = 0 := by
    rw [Finset.sum_range_succ']
    rw [Finset.sum_congr rfl fun k hk => htel k (Finset.mem_range.mp hk)]
    rw [Finset.sum_range_sub]
    simp only [hB, hG, hcf, pochhammer_zero, sub_self]
    push_cast
    ring
  unfold hahn terminatingHypergeometric
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  rw [show -(x + 1) = u - 1 by rw [hu]; ring, show -(x - 1) = u + 1 by rw [hu]; ring,
    show x + α + 1 = -(u - α - 1) by rw [hu]; ring, show (x : ℂ) - N = -(u + N) by rw [hu]; ring,
    show x - β - N - 1 = -(u + β + N + 1) by rw [hu]; ring, show x = -u by rw [hu]; ring]
  simp only [neg_neg]
  have hfin : ∀ v : ℂ, ∑ k ∈ Finset.range (n + 1), pochhammer (-(n : ℂ)) k *
      (pochhammer ((n : ℂ) + α + β + 1) k * pochhammer v k) /
          (pochhammer (α + 1) k * pochhammer (-(N : ℂ)) k) /
        (k ! : ℂ) = ∑ k ∈ Finset.range (n + 1), cf k * pochhammer v k := fun v =>
    Finset.sum_congr rfl fun k _ => by simp only [hcf, hs]; ring
  rw [hfin, hfin, hfin]
  clear_value B G cf u s
  have hexp : ∑ k ∈ Finset.range (n + 1), cf k * B k =
      (u - α - 1) * (u + N) * (∑ k ∈ Finset.range (n + 1), cf k * pochhammer (u - 1) k -
        ∑ k ∈ Finset.range (n + 1), cf k * pochhammer u k) +
      u * (u + β + N + 1) * (∑ k ∈ Finset.range (n + 1), cf k * pochhammer (u + 1) k -
        ∑ k ∈ Finset.range (n + 1), cf k * pochhammer u k) -
      n * (n + α + β + 1) * ∑ k ∈ Finset.range (n + 1), cf k * pochhammer u k := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hB]
    ring
  rw [hkey] at hexp
  linear_combination -hexp - (n * ∑ k ∈ Finset.range (n + 1), cf k * pochhammer u k) * hs

/-- 15.5.11 in `b` for the terminating function `₂F₁(-n, b; c; z)`, valid for every `z`
(both sides are polynomials in `z`). -/
theorem contiguous_b_neg_nat (n : ℕ) (b c z : ℂ) (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    (c - b) * ₂F₁ (-(n : ℂ)) (b - 1) c z +
      (2 * b - c + (-(n : ℂ) - b) * z) * ₂F₁ (-(n : ℂ)) b c z +
      b * (z - 1) * ₂F₁ (-(n : ℂ)) (b + 1) c z = 0 := by
  have key : (fun z : ℂ => (c - b) * ₂F₁ (-(n : ℂ)) (b - 1) c z +
      (2 * b - c + (-(n : ℂ) - b) * z) * ₂F₁ (-(n : ℂ)) b c z +
      b * (z - 1) * ₂F₁ (-(n : ℂ)) (b + 1) c z) = fun _ => 0 := by
    refine DLMF.Hypergeometric.eq_of_analyticOnNhd_univ_of_eqOn ?_ analyticOnNhd_const
      Metric.isOpen_ball ⟨0, Metric.mem_ball_self one_pos⟩ ?_
    · intro z _
      have h1 := analyticAt_gauss_neg_nat n (b - 1) c z
      have h2 := analyticAt_gauss_neg_nat n b c z
      have h3 := analyticAt_gauss_neg_nat n (b + 1) c z
      fun_prop
    intro z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    have h := contiguous_a (a := b) (b := -(n : ℂ)) (c := c) hc hz'
    simp only [DLMF.Hypergeometric.ordinaryHypergeometric_symm b (-(n : ℂ)) c,
      DLMF.Hypergeometric.ordinaryHypergeometric_symm (b - 1) (-(n : ℂ)) c,
      DLMF.Hypergeometric.ordinaryHypergeometric_symm (b + 1) (-(n : ℂ)) c] at h
    linear_combination h
  exact congrFun key z

/-- The Meixner polynomial as a terminating `₂F₁`. -/
theorem meixner_eq_hypergeometric (β c : ℂ) (n : ℕ) (x : ℂ) :
    meixner β c n x = ₂F₁ (-(n : ℂ)) (-x) β (1 - c⁻¹) := by
  unfold meixner terminatingHypergeometric
  rw [ordinaryHypergeometric_eq_sum_neg_nat]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, gaussHypergeometricCoeff]
  ring

/-- `contiguous_b_neg_nat` for every `c` off `{0, -1, …, -(n-1)}`, by analytic continuation
in `c`; this covers the Krawtchouk case `c = -N` with `n ≤ N`. -/
theorem contiguous_b_neg_nat' (n : ℕ) (b c z : ℂ) (hc : ∀ j : ℕ, j < n → c ≠ -(j : ℂ)) :
    (c - b) * ₂F₁ (-(n : ℂ)) (b - 1) c z +
      (2 * b - c + (-(n : ℂ) - b) * z) * ₂F₁ (-(n : ℂ)) b c z +
      b * (z - 1) * ₂F₁ (-(n : ℂ)) (b + 1) c z = 0 := by
  set S : Set ℂ := {c : ℂ | ∀ j : ℕ, j < n → c ≠ -(j : ℂ)} with hS
  have hSc : S = ((fun j : ℕ => -(j : ℂ)) '' {j : ℕ | j < n})ᶜ := by
    ext c
    simp only [hS, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · intro h j hj hje
      exact h j hj hje.symm
    · intro h j hj hje
      exact h j hj hje.symm
  have hconn : IsPreconnected S := by
    rw [hSc]
    exact (Set.Countable.isConnected_compl_of_one_lt_rank (by
      rw [Complex.rank_real_complex]; norm_num)
      ((Set.finite_Iio n).image _).countable).isPreconnected
  have h1 : (1 : ℂ) ∈ S := fun j _ h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hf : AnalyticOnNhd ℂ (fun c : ℂ => (c - b) * ₂F₁ (-(n : ℂ)) (b - 1) c z +
      (2 * b - c + (-(n : ℂ) - b) * z) * ₂F₁ (-(n : ℂ)) b c z +
      b * (z - 1) * ₂F₁ (-(n : ℂ)) (b + 1) c z) S := by
    intro c hc
    have g1 := DLMF.Hypergeometric.analyticOnNhd_gauss_neg_nat_param n (b - 1) z c hc
    have g2 := DLMF.Hypergeometric.analyticOnNhd_gauss_neg_nat_param n b z c hc
    have g3 := DLMF.Hypergeometric.analyticOnNhd_gauss_neg_nat_param n (b + 1) z c hc
    fun_prop
  have key := hf.eqOn_of_preconnected_of_eventuallyEq (g := fun _ => 0) analyticOnNhd_const hconn h1
    (by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by simp)] with c hcre
      exact contiguous_b_neg_nat n b c z (not_neg_nat_of_re_pos hcre))
  exact key hc

/-- The Krawtchouk polynomial as a terminating `₂F₁`. -/
theorem krawtchouk_eq_hypergeometric (p : ℂ) (N n : ℕ) (x : ℂ) :
    krawtchouk p N n x = ₂F₁ (-(n : ℂ)) (-x) (-(N : ℂ)) p⁻¹ := by
  unfold krawtchouk terminatingHypergeometric
  rw [ordinaryHypergeometric_eq_sum_neg_nat]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, gaussHypergeometricCoeff]
  ring

/-- Identity under the stated parameter and domain assumptions: `p * (x - N) * (krawtchouk p N n
(x + 1) - krawtchouk p N n x) + (p - 1) * x * (krawtchouk p N n (x - 1) - krawtchouk p N n x)
= n * krawtchouk p N n x`. -/
@[dlmf 18.22.T2]
theorem krawtchouk_difference_equation {p : ℂ} (hp : p ≠ 0) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    p * (x - N) * (krawtchouk p N n (x + 1) - krawtchouk p N n x) +
      (p - 1) * x * (krawtchouk p N n (x - 1) - krawtchouk p N n x) = n * krawtchouk p N n x := by
  have hc : ∀ j : ℕ, j < n → -(N : ℂ) ≠ -(j : ℂ) := fun j hj h => by
    have : (N : ℂ) = j := by linear_combination -h
    have : N = j := by exact_mod_cast this
    omega
  have R := contiguous_b_neg_nat' n (-x) (-(N : ℂ)) p⁻¹ hc
  simp only [krawtchouk_eq_hypergeometric, show -(x + 1) = -x - 1 by ring,
    show -(x - 1) = -x + 1 by ring]
  have hinv : p * p⁻¹ = 1 := mul_inv_cancel₀ hp
  linear_combination p * R + (-(x - n) * ₂F₁ (-(n : ℂ)) (-x) (-(N : ℂ)) p⁻¹ +
    x * ₂F₁ (-(n : ℂ)) (-x + 1) (-(N : ℂ)) p⁻¹) * hinv

/-- Identity under the stated parameter and domain assumptions: `c * (x + β) * (meixner β c n (x +
1) - meixner β c n x) + x * (meixner β c n (x - 1) - meixner β c n x) + n * (1 - c) * meixner
β c n x = 0`. -/
@[dlmf 18.22.T2]
theorem meixner_difference_equation {β c : ℂ} (hβ : 0 < β.re) (hc : c ≠ 0) (n : ℕ) (x : ℂ) :
    c * (x + β) * (meixner β c n (x + 1) - meixner β c n x) +
      x * (meixner β c n (x - 1) - meixner β c n x) + n * (1 - c) * meixner β c n x = 0 := by
  have hβ' : ∀ k : ℕ, β ≠ -(k : ℂ) := not_neg_nat_of_re_pos hβ
  have R := contiguous_b_neg_nat n (-x) β (1 - c⁻¹) hβ'
  simp only [meixner_eq_hypergeometric, show -(x + 1) = -x - 1 by ring,
    show -(x - 1) = -x + 1 by ring]
  have hinv : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  linear_combination c * R + (-x * ₂F₁ (-(n : ℂ)) (-x + 1) β (1 - c⁻¹) +
    (x - n) * ₂F₁ (-(n : ℂ)) (-x) β (1 - c⁻¹)) * hinv

/-- Forward difference of `(-x)_{k+1}` in `x`. -/
theorem pochhammer_neg_succ_sub (x : ℂ) (k : ℕ) :
    pochhammer (-(x + 1)) (k + 1) - pochhammer (-x) (k + 1) = -((k : ℂ) + 1) *
        pochhammer (-x) k := by
  rw [pochhammer_succ_left, pochhammer_succ, show -(x + 1) + 1 = -x by ring]
  ring

/-- `∏ (t)_{j+1} = (∏ t) ∏ (t+1)_j` over a list of parameters. -/
theorem prod_map_pochhammer_succ (L : List ℂ) (j : ℕ) :
    (L.map (fun t => pochhammer t (j + 1))).prod =
      L.prod * ((L.map (fun t => t + 1)).map (fun t => pochhammer t j)).prod := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih, pochhammer_succ_left]
    ring

/-- The forward difference in `x` of a terminating series whose last numerator parameter is
`-x`: the common step behind 18.22.19–18.22.25. -/
theorem terminatingHypergeometric_forward_difference (n : ℕ) (L B : List ℂ) (x z : ℂ) :
    terminatingHypergeometric (n + 1) (-((n + 1 : ℕ) : ℂ) :: (L ++ [-(x + 1)])) B z -
      terminatingHypergeometric (n + 1) (-((n + 1 : ℕ) : ℂ) :: (L ++ [-x])) B z =
    ((n + 1 : ℕ) : ℂ) * L.prod / B.prod * z *
      terminatingHypergeometric n (-(n : ℂ) :: (L.map (fun t => t + 1) ++ [-x]))
          (B.map (fun t => t + 1)) z := by
  unfold terminatingHypergeometric
  rw [← Finset.sum_sub_distrib, Finset.sum_range_succ', Finset.mul_sum]
  have h0 : (((-((n + 1 : ℕ) : ℂ) :: (L ++ [-(x + 1)])).map (fun t => pochhammer t 0)).prod /
        (B.map (fun t => pochhammer t 0)).prod * z ^ 0 / ((0 : ℕ).factorial : ℂ) -
      ((-((n + 1 : ℕ) : ℂ) :: (L ++ [-x])).map (fun t => pochhammer t 0)).prod /
        (B.map (fun t => pochhammer t 0)).prod * z ^ 0 / ((0 : ℕ).factorial : ℂ)) = 0 := by
    simp [pochhammer_zero]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast j.succ_ne_zero
  simp only [List.map_cons, List.map_append, List.map_nil, List.prod_cons, List.prod_append,
    List.prod_nil, mul_one]
  rw [prod_map_pochhammer_succ L j, prod_map_pochhammer_succ B j,
      pochhammer_succ_left (-((n + 1 : ℕ) : ℂ)),
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring, Nat.factorial_succ, pow_succ]
  push_cast
  have hd := pochhammer_neg_succ_sub x j
  have hinv : ((j : ℂ) + 1) * ((j : ℂ) + 1)⁻¹ = 1 := mul_inv_cancel₀ hj
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination
    (((n : ℂ) + 1) * (pochhammer (-(n : ℂ)) j * L.prod *
      ((L.map (fun t => t + 1)).map (fun t => pochhammer t j)).prod * (B.prod)⁻¹ *
      (((B.map (fun t => t + 1)).map (fun t => pochhammer t j)).prod)⁻¹ * z ^ j * z *
      ((j.factorial : ℂ))⁻¹) * pochhammer (-x) j) * hinv -
    (((n : ℂ) + 1) * (pochhammer (-(n : ℂ)) j * L.prod *
      ((L.map (fun t => t + 1)).map (fun t => pochhammer t j)).prod * (B.prod)⁻¹ *
      (((B.map (fun t => t + 1)).map (fun t => pochhammer t j)).prod)⁻¹ * z ^ j * z *
      ((j.factorial : ℂ))⁻¹) * ((j : ℂ) + 1)⁻¹) * hd

/-- `(-n)_{n+1} = 0`. -/
theorem pochhammer_neg_nat_succ (n : ℕ) : pochhammer (-(n : ℂ)) (n + 1) = 0 := by
  rw [pochhammer_succ]
  simp

/-- The difference of a terminating series in its truncation parameter: the companion of
`terminatingHypergeometric_forward_difference` for the first numerator parameter. -/
theorem terminatingHypergeometric_first_difference (n : ℕ) (L B : List ℂ) (z : ℂ) :
    terminatingHypergeometric (n + 1) (-((n + 1 : ℕ) : ℂ) :: L) B z -
        terminatingHypergeometric n (-(n : ℂ) :: L) B z =
      -(L.prod / B.prod * z) *
          terminatingHypergeometric n (-(n : ℂ) :: L.map (fun t => t + 1))
              (B.map (fun t => t + 1)) z := by
  unfold terminatingHypergeometric
  have hext : ∑ k ∈ Finset.range (n + 1), ((-(n : ℂ) :: L).map (fun t => pochhammer t k)).prod /
        (B.map (fun t => pochhammer t k)).prod * z ^ k / (k.factorial : ℂ) =
      ∑ k ∈ Finset.range (n + 1 + 1), ((-(n : ℂ) :: L).map (fun t => pochhammer t k)).prod /
        (B.map (fun t => pochhammer t k)).prod * z ^ k / (k.factorial : ℂ) := by
    rw [Finset.sum_range_succ _ (n + 1)]
    simp [pochhammer_neg_nat_succ]
  rw [hext, ← Finset.sum_sub_distrib, Finset.sum_range_succ', Finset.mul_sum]
  simp only [List.map_cons, List.prod_cons]
  have h0 : (pochhammer (-((n + 1 : ℕ) : ℂ)) 0 * (L.map (fun t => pochhammer t 0)).prod /
        (B.map (fun t => pochhammer t 0)).prod * z ^ 0 / ((0 : ℕ).factorial : ℂ) -
      pochhammer (-(n : ℂ)) 0 * (L.map (fun t => pochhammer t 0)).prod /
        (B.map (fun t => pochhammer t 0)).prod * z ^ 0 / ((0 : ℕ).factorial : ℂ)) = 0 := by
    simp [pochhammer_zero]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast j.succ_ne_zero
  rw [prod_map_pochhammer_succ L j, prod_map_pochhammer_succ B j, Nat.factorial_succ, pow_succ]
  have hd := pochhammer_neg_succ_sub (n : ℂ) j
  push_cast
  have hinv : ((j : ℂ) + 1) * ((j : ℂ) + 1)⁻¹ = 1 := mul_inv_cancel₀ hj
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination
    (-(L.prod * ((L.map (fun t => t + 1)).map (fun t => pochhammer t j)).prod * (B.prod)⁻¹ *
      (((B.map (fun t => t + 1)).map (fun t => pochhammer t j)).prod)⁻¹ * z ^ j * z *
      ((j.factorial : ℂ))⁻¹) * pochhammer (-(n : ℂ)) j) * hinv +
    ((L.prod * ((L.map (fun t => t + 1)).map (fun t => pochhammer t j)).prod * (B.prod)⁻¹ *
      (((B.map (fun t => t + 1)).map (fun t => pochhammer t j)).prod)⁻¹ * z ^ j * z *
      ((j.factorial : ℂ))⁻¹) * ((j : ℂ) + 1)⁻¹) * hd

/-- `C_{n+1}(x) - C_n(x) = -(x/a) C_n(x - 1)`, the Charlier companion of 18.22.25 in `n`. -/
theorem charlier_first_difference (a : ℂ) (n : ℕ) (x : ℂ) :
    charlier a (n + 1) x - charlier a n x = -(x / a) * charlier a n (x - 1) := by
  unfold charlier
  have h := terminatingHypergeometric_first_difference n [-x] [] (-a⁻¹)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    show -x + 1 = -(x - 1) by ring] at h
  rw [h]
  ring

/-- Identity under the stated parameter and domain assumptions: `hahn α β (N + 1) (n + 1) (x + 1)
- hahn α β (N + 1) (n + 1) x = -((n + 1) * (n + α + β + 2)) / ((α + 1) * (N + 1)) * hahn (α +
1) (β + 1) N n x`. -/
@[dlmf 18.22.E19]
theorem hahn_forward_difference {α β : ℂ} (hα : -1 < α.re) {N n : ℕ} (x : ℂ) :
    hahn α β (N + 1) (n + 1) (x + 1) - hahn α β (N + 1) (n + 1) x =
      -((n + 1) * (n + α + β + 2)) / ((α + 1) * (N + 1)) * hahn (α + 1) (β + 1) N n x := by
  unfold hahn
  have h := terminatingHypergeometric_forward_difference n [((n + 1 : ℕ) : ℂ) + α + β + 1]
    [α + 1, -((N + 1 : ℕ) : ℂ)] x 1
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.cons_append,
    List.nil_append, mul_one,
    show ((n + 1 : ℕ) : ℂ) + α + β + 1 + 1 = (n : ℂ) + (α + 1) + (β + 1) + 1 by push_cast; ring,
    show -((N + 1 : ℕ) : ℂ) + 1 = -(N : ℂ) by push_cast; ring] at h
  rw [h]
  have hα0 : α + 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hN : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast N.succ_ne_zero
  push_cast
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `krawtchouk p (N + 1) (n + 1) (x +
1) - krawtchouk p (N + 1) (n + 1) x = -(n + 1) / (p * (N + 1)) * krawtchouk p N n x`. -/
@[dlmf 18.22.E21]
theorem krawtchouk_forward_difference {p : ℂ} (hp : p ≠ 0) {N n : ℕ} (x : ℂ) :
    krawtchouk p (N + 1) (n + 1) (x + 1) - krawtchouk p (N + 1) (n + 1) x =
      -(n + 1) / (p * (N + 1)) * krawtchouk p N n x := by
  unfold krawtchouk
  have h := terminatingHypergeometric_forward_difference n [] [-((N + 1 : ℕ) : ℂ)] x p⁻¹
  simp only [List.nil_append, List.map_nil, List.prod_nil, List.map_cons, List.prod_cons,
    show -((N + 1 : ℕ) : ℂ) + 1 = -(N : ℂ) by push_cast; ring] at h
  rw [h]
  have hN : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast N.succ_ne_zero
  push_cast
  field_simp

/-- Identity under the stated parameter and domain assumptions: `meixner β c (n + 1) (x + 1) -
meixner β c (n + 1) x = -(n + 1) * (1 - c) / (β * c) * meixner (β + 1) c n x`. -/
@[dlmf 18.22.E23]
theorem meixner_forward_difference {β c : ℂ} (hβ : 0 < β.re) (hc : c ≠ 0) (n : ℕ) (x : ℂ) :
    meixner β c (n + 1) (x + 1) - meixner β c (n + 1) x =
      -(n + 1) * (1 - c) / (β * c) * meixner (β + 1) c n x := by
  unfold meixner
  have h := terminatingHypergeometric_forward_difference n [] [β] x (1 - c⁻¹)
  simp only [List.nil_append, List.map_nil, List.prod_nil, List.map_cons, List.prod_cons] at h
  rw [h]
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0] at hβ
    simp at hβ
  push_cast
  field_simp
  ring

/-- Identity under the stated parameter and domain assumptions: `charlier a (n + 1) (x + 1) -
charlier a (n + 1) x = -(n + 1) / a * charlier a n x`. -/
@[dlmf 18.22.E25]
theorem charlier_forward_difference {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    charlier a (n + 1) (x + 1) - charlier a (n + 1) x = -(n + 1) / a * charlier a n x := by
  unfold charlier
  have h := terminatingHypergeometric_forward_difference n [] [] x (-a⁻¹)
  simp only [List.nil_append, List.map_nil, List.prod_nil] at h
  rw [h]
  push_cast
  field_simp

/-- Identity under the stated parameter and domain assumptions: `a * (charlier a n (x + 1) -
charlier a n x) + x * (charlier a n (x - 1) - charlier a n x) + n * charlier a n x = 0`. -/
@[dlmf 18.22.T2]
theorem charlier_difference_equation {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    a * (charlier a n (x + 1) - charlier a n x) +
      x * (charlier a n (x - 1) - charlier a n x) + n * charlier a n x = 0 := by
  cases n with
  | zero => simp [charlier, terminatingHypergeometric, pochhammer_zero]
  | succ m =>
    have h1 := charlier_forward_difference ha m x
    have h2 := charlier_forward_difference ha m (x - 1)
    rw [sub_add_cancel] at h2
    have h3 := charlier_first_difference a m x
    have h1' : a * (charlier a (m + 1) (x + 1) - charlier a (m + 1) x) =
        -((m : ℂ) + 1) * charlier a m x := by
      rw [h1]
      field_simp
    have h2' : a * (charlier a (m + 1) x - charlier a (m + 1) (x - 1)) =
        -((m : ℂ) + 1) * charlier a m (x - 1) := by
      rw [h2]
      field_simp
    have h3' : a * (charlier a (m + 1) x - charlier a m x) = -x * charlier a m (x - 1) := by
      rw [h3]
      field_simp
    push_cast
    apply mul_left_cancel₀ ha
    linear_combination a * h1' - x * h2' + ((m : ℂ) + 1) * h3'

/-- Identity under the stated parameter and domain assumptions: `(n + 2 : ℂ) * meixnerPollaczek
lam phi (n + 2) x = 2 * (x * sin phi + (n + lam + 1) * cos phi) * meixnerPollaczek lam phi (n
+ 1) x - (n + 2 * lam) * meixnerPollaczek lam phi n x`. -/
@[dlmf 18.22.E8]
theorem meixnerPollaczek_recurrence {lam : ℂ} (hlam : 0 < lam.re) (phi : ℂ) (n : ℕ) (x : ℂ) :
    (n + 2 : ℂ) * meixnerPollaczek lam phi (n + 2) x =
      2 * (x * sin phi + (n + lam + 1) * cos phi) * meixnerPollaczek lam phi (n + 1) x -
      (n + 2 * lam) * meixnerPollaczek lam phi n x := by
  have hc : ∀ k : ℕ, 2 * lam ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hcont :=
    Hypergeometric.contiguous_a_neg_nat hc n (b := lam + I * x) (1 - cexp (-2 * I * phi))
  unfold meixnerPollaczek
  rw [terminatingHypergeometric_eq_ordinaryHypergeometric,
      terminatingHypergeometric_eq_ordinaryHypergeometric,
    terminatingHypergeometric_eq_ordinaryHypergeometric]
  push_cast at hcont ⊢
  set F2 := ₂F₁ (-((n : ℂ) + 2)) (lam + I * x) (2 * lam) (1 - cexp (-2 * I * phi))
  set F1 := ₂F₁ (-((n : ℂ) + 1)) (lam + I * x) (2 * lam) (1 - cexp (-2 * I * phi))
  set F0 := ₂F₁ (-(n : ℂ)) (lam + I * x) (2 * lam) (1 - cexp (-2 * I * phi))
  set u := cexp (I * phi) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  have e2 : cexp (-2 * I * phi) = (u ^ 2)⁻¹ := by
    rw [hu, ← Complex.exp_nat_mul, ← Complex.exp_neg]; congr 1; push_cast; ring
  have en2 : cexp (I * (n + 2) * phi) = cexp (I * n * phi) * u ^ 2 := by
    rw [hu, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
  have en1 : cexp (I * (n + 1) * phi) = cexp (I * n * phi) * u := by
    rw [hu, ← Complex.exp_add]; congr 1; ring
  have hcos : cos phi = (u + u⁻¹) / 2 := by
    rw [Complex.cos, hu, ← Complex.exp_neg]; congr 2 <;> ring_nf
  have hsin : sin phi = (u⁻¹ - u) * I / 2 := by
    rw [Complex.sin, hu, ← Complex.exp_neg]; congr 3 <;> ring_nf
  have hp2 : pochhammer (2 * lam) (n + 2) = pochhammer (2 * lam) n * (2 * lam + n) *
      (2 * lam + (n + 1)) := by
    rw [pochhammer_succ, pochhammer_succ]; push_cast; ring
  have hp1 : pochhammer (2 * lam) (n + 1) = pochhammer (2 * lam) n * (2 * lam + n) := by
    rw [pochhammer_succ]
  have hf2 : ((n + 2) ! : ℂ) = (n + 2) * (n + 1) * n ! := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have hf1 : ((n + 1) ! : ℂ) = (n + 1) * n ! := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have hn2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  rw [e2] at hcont
  rw [en2, en1, hcos, hsin, hp2, hp1, hf2, hf1]
  set E := cexp (I * n * phi)
  field_simp at hcont ⊢
  linear_combination (pochhammer (2 * lam) n * (2 * lam + n) * E) * hcont

/-- Identity under the stated parameter and domain assumptions: `(meixnerPollaczek lam phi (n + 1)
(x + I / 2) - meixnerPollaczek lam phi (n + 1) (x - I / 2)) / I = 2 * sin phi *
meixnerPollaczek (lam + 1 / 2) phi n x`. -/
@[dlmf 18.22.E29]
theorem meixnerPollaczek_central_difference {lam : ℂ} (hlam : 0 < lam.re) (phi : ℂ)
    (n : ℕ) (x : ℂ) :
    (meixnerPollaczek lam phi (n + 1) (x + I / 2) -
        meixnerPollaczek lam phi (n + 1) (x - I / 2)) / I =
      2 * sin phi * meixnerPollaczek (lam + 1 / 2) phi n x := by
  have h2 : 0 < (2 * lam).re := by simp; linarith
  have h2l : 2 * lam ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have hl0 : lam ≠ 0 := fun h => by rw [h] at hlam; simp at hlam
  have hp : ∀ k : ℕ, pochhammer (2 * lam + 1) k ≠ 0 := fun k =>
    pochhammer_ne_zero_of_re_pos (by simp; linarith) k
  unfold meixnerPollaczek terminatingHypergeometric
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [pochhammer_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one,
      sub_self, add_zero,
    pow_zero]
  rw [show lam + I * (x + I / 2) = (lam + I * x) - 1 / 2 by linear_combination (1 / 2 : ℂ) * I_sq,
    show lam + I * (x - I / 2) = (lam + I * x) + 1 / 2 by linear_combination (-1 / 2 : ℂ) * I_sq]
  rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have key := pochhammer_half_sub (lam + I * x) k
  rw [← sub_div, ← sub_mul, ← sub_div, ← mul_sub, key]
  have hS := exp_mul_one_sub_exp phi
  rw [pochhammer_succ_left (2 * lam), pochhammer_succ_left (2 * lam) k,
      pochhammer_succ_left (-((n + 1 : ℕ) : ℂ)),
    Nat.factorial_succ, Nat.factorial_succ, show 2 * (lam + 1 / 2) = 2 * lam + 1 by ring,
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring,
    show lam + I * x + 1 / 2 = lam + 1 / 2 + I * x by ring, pow_succ,
    show I * ((n + 1 : ℕ) : ℂ) * phi = I * n * phi + I * phi by push_cast; ring, exp_add]
  have hS' : sin phi = exp (I * phi) * (1 - exp (-2 * I * phi)) / (2 * I) := by
    rw [hS]; field_simp
  rw [hS']
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have := hp k; have := hp n
  push_cast
  field_simp

/-- `∑ₙ C(N,n) (-n)ₖ zⁿ w^{N-n} = (-N)ₖ zᵏ (z+w)^{N-k}` for `k ≤ N`: factorial moments of a
binomial distribution. -/
theorem sum_choose_mul_pochhammer_neg_nat_mul_pow {N k : ℕ} (hk : k ≤ N) (z w : ℂ) :
    ∑ n ∈ Finset.range (N + 1), (N.choose n : ℂ) * pochhammer (-(n : ℂ)) k * z ^ n * w ^ (N - n) =
      pochhammer (-(N : ℂ)) k * z ^ k * (z + w) ^ (N - k) := by
  rw [show N + 1 = k + (N - k + 1) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero fun n hn => by
    rw [pochhammer_neg_nat_eq_zero (by simpa using hn)]; simp, zero_add]
  rw [add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ N - k := by simp at hm; omega
  rw [pochhammer_neg_coe_nat, pochhammer_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose, pow_add, show N - (k + m) = N - k - m by omega]
  have hc := Nat.choose_mul (n := N) (k := k + m) (s := k) (by omega)
  rw [show k + m - k = m by omega] at hc
  have hc' : (N.choose (k + m) : ℂ) * ((k + m).choose k) = N.choose k * (N - k).choose m := by
    exact_mod_cast hc
  push_cast
  linear_combination (-1 : ℂ) ^ k * k ! * z ^ k * z ^ m * w ^ (N - k - m) * hc'

/-- `∑ₙ C(N,n) (-n)ₖ zⁿ = (-N)ₖ zᵏ (1+z)^{N-k}` for `k ≤ N`. -/
theorem sum_choose_mul_pochhammer_neg_nat {N k : ℕ} (hk : k ≤ N) (z : ℂ) :
    ∑ n ∈ Finset.range (N + 1), (N.choose n : ℂ) * pochhammer (-(n : ℂ)) k * z ^ n =
      pochhammer (-(N : ℂ)) k * z ^ k * (1 + z) ^ (N - k) := by
  simpa [add_comm z] using sum_choose_mul_pochhammer_neg_nat_mul_pow hk z 1

/-- Formula under the stated hypotheses: `∑ n ∈ Finset.range (N + 1), (N.choose n : ℂ) *
krawtchouk p N n x * z ^ n = (1 - (1 - p) / p * z) ^ x * (1 + z) ^ (N - x)`. -/
@[dlmf 18.23.E3]
theorem krawtchouk_generating_function {p : ℂ} (hp : p ≠ 0) {N x : ℕ} (hx : x ≤ N) (z : ℂ) :
    ∑ n ∈ Finset.range (N + 1), (N.choose n : ℂ) * krawtchouk p N n x * z ^ n =
      (1 - (1 - p) / p * z) ^ x * (1 + z) ^ (N - x) := by
  unfold krawtchouk
  simp_rw [terminatingHypergeometric_two_neg_nat_swap _ x, terminatingHypergeometric,
      Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ k ∈ Finset.range (x + 1), ∑ n ∈ Finset.range (N + 1),
      (N.choose n : ℂ) * ((([-(x : ℂ), -(n : ℂ)].map fun t => pochhammer t k).prod /
        ([-(N : ℂ)].map fun t => pochhammer t k).prod * p⁻¹ ^ k / k !)) * z ^ n =
      (1 + z) ^ (N - x) * ((x.choose k : ℂ) * (-(z / p)) ^ k * (1 + z) ^ (x - k)) := by
    intro k hk
    have hkx : k ≤ x := by simp at hk; omega
    have hN : pochhammer (-(N : ℂ)) k ≠ 0 := by
      rw [pochhammer_neg_coe_nat]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr (by omega)).ne')
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have hs := sum_choose_mul_pochhammer_neg_nat (show k ≤ N by omega) z
    rw [Finset.sum_congr rfl (g := fun n : ℕ => (pochhammer (-(x : ℂ)) k / pochhammer (-(N : ℂ)) k *
      p⁻¹ ^ k / k !) * ((N.choose n : ℂ) * pochhammer (-(n : ℂ)) k * z ^ n)) (fun n _ => by ring),
      ← Finset.mul_sum, hs, pochhammer_neg_coe_nat x, Nat.descFactorial_eq_factorial_mul_choose,
      show N - k = (N - x) + (x - k) by omega, pow_add]
    have hk' : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, mul_comm]
  congr 1
  rw [show 1 - (1 - p) / p * z = -(z / p) + (1 + z) by field_simp; ring, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `∑ₙ (β)ₙ (-n)ₖ zⁿ / n! = (β)ₖ (-z)ᵏ (1 - z)^{-β-k}`. -/
theorem hasSum_pochhammer_mul_pochhammer_neg_nat {β z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    HasSum (fun n : ℕ => pochhammer β n / n ! * pochhammer (-(n : ℂ)) k * z ^ n)
      (pochhammer β k * (-z) ^ k * (1 - z) ^ (-(β + k))) := by
  have hb := (hasSum_pochhammer_div_factorial (β := β + k) hz).mul_left (pochhammer β k * (-z) ^ k)
  have h0 : ∑ i ∈ Finset.range k, pochhammer β i / i ! * pochhammer (-(i : ℂ)) k * z ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [pochhammer_neg_nat_eq_zero (by simpa using hi)]; simp
  have key := (hasSum_nat_add_iff
      (f := fun n : ℕ => pochhammer β n / n ! * pochhammer (-(n : ℂ)) k * z ^ n)
    k (g := pochhammer β k * (-z) ^ k * (1 - z) ^ (-(β + k)))).mp ?_
  · rwa [h0, add_zero] at key
  refine hb.congr_fun fun n => ?_
  have hn' : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hnk : ((n + k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd : ((n + k).descFactorial k : ℂ) * n ! = (n + k) ! := by
    have := Nat.factorial_mul_descFactorial (show k ≤ n + k by omega)
    rw [show n + k - k = n by omega] at this
    exact_mod_cast (mul_comm _ _).trans this
  rw [pochhammer_neg_coe_nat, add_comm n k, pochhammer_add, neg_pow, pow_add, add_comm k n]
  field_simp
  linear_combination (-1) ^ k * pochhammer β k * pochhammer (β + k) n * z ^ n * z ^ k * hd

/-- The series with terms `(fun n : ℕ => pochhammer β n / n.factorial * meixner β c n x * z ^ n)`
converges to `((1 - z / c) ^ x * (1 - z) ^ (-(x : ℂ) - β))`. -/
@[dlmf 18.23.E4]
theorem meixner_generating_function {β c : ℂ} (hβ : 0 < β.re) (hc : c ≠ 0) (x : ℕ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => pochhammer β n / n.factorial * meixner β c n x * z ^ n)
      ((1 - z / c) ^ x * (1 - z) ^ (-(x : ℂ) - β)) := by
  have hβk : ∀ k, pochhammer β k ≠ 0 := pochhammer_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hβ)
  have h1z : (1 : ℂ) - z ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this, norm_one] at hz
    exact lt_irrefl _ hz
  set u : ℂ := 1 - c⁻¹
  unfold meixner
  simp_rw [terminatingHypergeometric_two_neg_nat_swap _ x, terminatingHypergeometric,
      Finset.mul_sum, Finset.sum_mul]
  have h := hasSum_sum (s := Finset.range (x + 1)) (fun k _ =>
    (hasSum_pochhammer_mul_pochhammer_neg_nat (β := β) hz k).mul_left
      (pochhammer (-(x : ℂ)) k / pochhammer β k * u ^ k / k !))
  convert h using 1
  · funext n
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  · have hsplit : ∀ k : ℕ, (1 - z) ^ (-(β + k)) = (1 - z) ^ (-β) * ((1 - z) ^ k)⁻¹ := by
      intro k
      rw [neg_add, cpow_add _ _ h1z, cpow_neg _ (k : ℂ), cpow_natCast]
    have hx : (1 - z) ^ (-(x : ℂ) - β) = (1 - z) ^ (-β) * ((1 - z) ^ x)⁻¹ := by
      rw [show -(x : ℂ) - β = -β + -(x : ℂ) by ring, cpow_add _ _ h1z, cpow_neg _ (x : ℂ),
        cpow_natCast]
    have hbin := sum_pochhammer_neg_nat_div_factorial_mul_pow x (-(u * z) / (1 - z))
    rw [show (1 : ℂ) - -(u * z) / (1 - z) = (1 - z / c) / (1 - z) by
      simp only [u]; field_simp; ring, div_pow] at hbin
    have hterm : ∀ k ∈ Finset.range (x + 1), pochhammer (-(x : ℂ)) k /
        pochhammer β k * u ^ k / k ! *
        (pochhammer β k * (-z) ^ k * (1 - z) ^ (-(β + k))) =
        (1 - z) ^ (-β) * (pochhammer (-(x : ℂ)) k / k ! * (-(u * z) / (1 - z)) ^ k) := by
      intro k _
      rw [hsplit, div_pow]
      have := hβk k
      field_simp
      rw [show -(z * u) = u * -z by ring, mul_pow]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hbin, hx]
    field_simp

end DLMF.OrthogonalPolynomials
end
end
