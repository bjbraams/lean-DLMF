/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.PollaczekMoments
public import DLMF.Confluent.Recurrence
public import DLMF.OrthogonalPolynomials.BinomialSeries

/-!
# The Hahn class: definitions, orthogonality, differences, and generating functions

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology
open DLMF.Hypergeometric
open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

/-- A terminating hypergeometric sum, with an explicit cutoff. This implements
DLMF's convention when a lower parameter is a negative integer. -/
def terminatingHG (n : ℕ) (a b : List ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (a.map (fun t => poch t k)).prod / (b.map (fun t => poch t k)).prod *
      z ^ k / (k.factorial : ℂ)

/-- A negative integral first upper parameter makes the finite sum a genuine infinite sum. -/
theorem terminatingHG_hasSum_neg_nat (n : ℕ) (a b : List ℂ) (z : ℂ) :
    HasSum (fun k : ℕ => (((-(n : ℂ) :: a).map (fun t => poch t k)).prod /
      (b.map (fun t => poch t k)).prod * z ^ k / (k.factorial : ℂ)))
      (terminatingHG n (-(n : ℂ) :: a) b z) := by
  unfold terminatingHG
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  have hnk : n < k := by simpa using hk
  simp [poch_neg_nat_eq_zero hnk]

/-- Pochhammer symbols at points of positive real part do not vanish. -/
theorem poch_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) (k : ℕ) : poch z k ≠ 0 :=
  poch_ne_zero_of_not_neg_nat (fun j h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) k

/-- The forward difference of a Pochhammer symbol in a shifted argument. -/
theorem poch_half_sub (w : ℂ) (k : ℕ) :
    poch (w - 1 / 2) (k + 1) - poch (w + 1 / 2) (k + 1) = -(k + 1) * poch (w + 1 / 2) k := by
  rw [poch_succ_left (w - 1 / 2), poch_succ (w + 1 / 2), show w - 1 / 2 + 1 = w + 1 / 2 by ring]
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
    exp (I * phi) * (-I * (w - 2 * lam)) * (poch (w - 1) (k + 1) - poch w (k + 1)) +
      exp (-I * phi) * (-I * w) * (poch (w + 1) (k + 1) - poch w (k + 1)) +
      2 * n * sin phi * poch w (k + 1) =
      2 * (n - (k + 1)) * sin phi * poch w (k + 1) -
        I * (k + 1) * exp (I * phi) * (k + 2 * lam) * poch w k := by
  have hS := exp_mul_one_sub_exp phi
  have h1 : exp (I * phi) * exp (-2 * I * phi) = exp (-I * phi) := by rw [← exp_add]; ring_nf
  have hsin : 2 * I * sin phi = exp (I * phi) - exp (-I * phi) := by
    rw [← hS, mul_sub, mul_one, h1]
  have hrel : poch w k * (w + k) = w * poch (w + 1) k := by
    rw [← poch_succ, poch_succ_left]
  rw [poch_succ_left (w - 1), show w - 1 + 1 = w by ring, poch_succ w k, poch_succ (w + 1) k]
  linear_combination (-(I) * poch w k * ((k : ℂ) + 1) * (k + w)) * hsin +
    (I * exp (-I * phi) * (k + w + 1)) * hrel +
    (2 * sin phi * poch w k * ((k : ℂ) + 1) * (w + k)) * I_sq

/-- The continuous Hahn difference operator on the basis `(w)_{k+1}`, `w = a + i x`. -/
theorem ch_basis_succ (a b c d w : ℂ) (n k : ℕ) :
    -((w - a - c) * (w - a - d)) * (poch (w - 1) (k + 1) - poch w (k + 1)) -
      w * (w - a + b) * (poch (w + 1) (k + 1) - poch w (k + 1)) +
      n * (n + a + b + c + d - 1) * poch w (k + 1) =
      (n - (k + 1)) * (n + (k + 1) + a + b + c + d - 1) * poch w (k + 1) +
        (k + 1) * (a + c + k) * (a + d + k) * poch w k := by
  have hrel : poch w k * (w + k) = w * poch (w + 1) k := by
    rw [← poch_succ, poch_succ_left]
  rw [poch_succ_left (w - 1), show w - 1 + 1 = w by ring, poch_succ w k, poch_succ (w + 1) k]
  linear_combination (w - a + b) * (k + w + 1) * hrel

/-- The Hahn difference operator on the basis `(u)_{k+1}`, `u = -x`. -/
theorem hahn_basis_succ (α β N u : ℂ) (n k : ℕ) :
    (u - α - 1) * (u + N) * (poch (u - 1) (k + 1) - poch u (k + 1)) +
      u * (u + β + N + 1) * (poch (u + 1) (k + 1) - poch u (k + 1)) -
      n * (n + α + β + 1) * poch u (k + 1) =
      (k + 1 - n) * (k + 1 + n + α + β + 1) * poch u (k + 1) +
        (k + 1) * (N - k) * (α + k + 1) * poch u k := by
  have hrel : poch u k * (u + k) = u * poch (u + 1) k := by
    rw [← poch_succ, poch_succ_left]
  rw [poch_succ_left (u - 1), show u - 1 + 1 = u by ring, poch_succ u k, poch_succ (u + 1) k]
  linear_combination (-((k + u + 1) * (N + β + u + 1))) * hrel

/-- The Hahn polynomial `Q_n(x; α, β, N) = ₃F₂(-n, n+α+β+1, -x; α+1, -N; 1)` (DLMF 18.20.5). -/
@[dlmf 18.20.E5]
def hahn (α β : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), n + α + β + 1, -x] [α + 1, -(N : ℂ)] 1

/-- The Krawtchouk polynomial `K_n(x; p, N) = ₂F₁(-n, -x; -N; 1/p)` (DLMF 18.20.6). -/
@[dlmf 18.20.E6]
def krawtchouk (p : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), -x] [-(N : ℂ)] p⁻¹

/-- The Meixner polynomial `M_n(x; β, c) = ₂F₁(-n, -x; β; 1 - 1/c)` (DLMF 18.20.7). -/
@[dlmf 18.20.E7]
def meixner (β c : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), -x] [β] (1 - c⁻¹)

/-- The Charlier polynomial `C_n(x; a) = ₂F₀(-n, -x; ; -1/a)` (DLMF 18.20.8). -/
@[dlmf 18.20.E8]
def charlier (a : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), -x] [] (-a⁻¹)

/-- The four-parameter polynomial; the orthogonality regime has `c = conj a`,
`d = conj b`. -/
@[dlmf 18.20.E9]
def continuousHahn (a b c d : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  I ^ n * poch (a + c) n * poch (a + d) n / n.factorial *
    terminatingHG n [-(n : ℂ), n + a + b + c + d - 1, a + I * x] [a + c, a + d] 1

/-- The Meixner–Pollaczek polynomial
`P_n^{(λ)}(x; φ) = (2λ)_n/n! e^{inφ} ₂F₁(-n, λ+ix; 2λ; 1 - e^{-2iφ})` (DLMF 18.20.10). -/
@[dlmf 18.20.E10]
def meixnerPollaczek (lam phi : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (2 * lam) n / n.factorial * exp (I * n * phi) *
    terminatingHG n [-(n : ℂ), lam + I * x] [2 * lam] (1 - exp (-2 * I * phi))

/-- The continuous Hahn weight `Γ(a+ix) Γ(b+ix) Γ(ā-ix) Γ(b̄-ix)` (DLMF 18.19.2). -/
@[dlmf 18.19.E2]
def continuousHahnWeight (a b : ℂ) (x : ℂ) : ℂ :=
  Gamma (a + I * x) * Gamma (b + I * x) * Gamma (star a - I * x) * Gamma (star b - I * x)

/-- The Meixner–Pollaczek weight `Γ(λ+ix) Γ(λ-ix) e^{(2φ-π)x}` (DLMF 18.19.7). -/
@[dlmf 18.19.E7]
def meixnerPollaczekWeight (lam phi : ℂ) (x : ℂ) : ℂ :=
  Gamma (lam + I * x) * Gamma (lam - I * x) * exp ((2 * phi - Real.pi) * x)

/-- The continuous Hahn normalization times its finite Pochhammer sum. -/
theorem continuousHahn_eq_hahnSum (a b c d : ℂ) (n : ℕ) (x : ℝ) :
    continuousHahn a b c d n x =
      (I ^ n * poch (a + c) n * poch (a + d) n / n.factorial) *
        HahnMoments.hahnSum a b c d n x := by
  unfold continuousHahn terminatingHG HahnMoments.hahnSum
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, one_pow, mul_one]
  ring

@[dlmf 18.19.E4]
theorem continuousHahn_orthogonal {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {m n : ℕ} (hmn : m ≠ n) :
    ∫ x : ℝ, continuousHahn a b (star a) (star b) m x *
      continuousHahn a b (star a) (star b) n x * continuousHahnWeight a b x = 0 := by
  let C (k : ℕ) : ℂ := I ^ k * poch (a + star a) k * poch (a + star b) k / k.factorial
  have he (x : ℝ) : continuousHahn a b (star a) (star b) m x *
      continuousHahn a b (star a) (star b) n x * continuousHahnWeight a b x =
        (C m * C n) * (HahnMoments.hahnSum a b (star a) (star b) m x *
          HahnMoments.hahnSum a b (star a) (star b) n x * HahnMoments.weight a b (star a) (star b) x) := by
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
      (poch (2*(lam:ℂ)) n/n.factorial*(I*PollaczekMoments.phase (2*phi-π))^n)*
        PollaczekMoments.poly lam (2*phi-π) n x := by
  have he : exp (I*(n:ℂ)*(phi:ℂ)) = (I*PollaczekMoments.phase (2*phi-π))^n := by
    rw [← pollaczek_phase_angle, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [meixnerPollaczek, he, pollaczek_argument_angle]
  congr 1
  unfold terminatingHG PollaczekMoments.poly
  apply Finset.sum_congr rfl
  intro k hk
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hf : (k.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp

@[dlmf 18.19.E9]
theorem meixnerPollaczek_orthogonality {lam phi : ℝ} (hlam : 0 < lam) (hphi : 0 < phi) (hphiπ : phi < Real.pi) (m n : ℕ) :
    ∫ x : ℝ, meixnerPollaczek lam phi m x * meixnerPollaczek lam phi n x *
      meixnerPollaczekWeight lam phi x =
      if m = n then 2 * Real.pi * Gamma (n + 2 * (lam : ℂ)) /
        ((2 * sin (phi : ℂ)) ^ (2 * (lam : ℂ)) * n.factorial) else 0 := by
  have hθ : |2*phi-π| < π := by rw [abs_lt]; constructor <;> linarith
  let C (k : ℕ) : ℂ := poch (2*(lam:ℂ)) k/k.factorial*(I*PollaczekMoments.phase (2*phi-π))^k
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
    change (poch (2*(lam:ℂ)) n/n.factorial*(I*PollaczekMoments.phase (2*phi-π))^n)^2 * _ = _
    rw [PollaczekMoments.normalized_square hlam hθ, pollaczek_scale_angle, add_comm (n:ℂ)]
  · rw [ite_eq_right hmn, PollaczekMoments.poly_orthogonal hlam hθ hmn, mul_zero]

/-- A two-numerator terminating sum is a terminating Gauss series. -/
theorem terminatingHG_eq_ordinaryHypergeometric (n : ℕ) (b c z : ℂ) :
    terminatingHG n [-(n : ℂ), b] [c] z = ₂F₁ (-(n : ℂ)) b c z := by
  rw [ordinaryHypergeometric_eq_sum_neg_nat]
  unfold terminatingHG gaussHGCoeff
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

/-- A second terminating upper parameter permits extending the cutoff to the larger index. -/
theorem terminatingHG_two_neg_nat (n m : ℕ) (b : List ℂ) (z : ℂ) :
    terminatingHG n [-(n : ℂ), -(m : ℂ)] b z =
      ∑ k ∈ Finset.range (max n m + 1), poch (-(n : ℂ)) k * poch (-(m : ℂ)) k /
        (b.map (fun t => poch t k)).prod * z ^ k / (k.factorial : ℂ) := by
  simp only [terminatingHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (le_max_left n m) 1))
  intro k _ hk
  have hnk : n < k := by
    rw [Finset.mem_range] at hk
    omega
  simp [poch_neg_nat_eq_zero hnk]

/-- Symmetry remains valid even when a lower parameter is a nonpositive integer. -/
theorem terminatingHG_two_neg_nat_swap (n m : ℕ) (b : List ℂ) (z : ℂ) :
    terminatingHG n [-(n : ℂ), -(m : ℂ)] b z =
      terminatingHG m [-(m : ℂ), -(n : ℂ)] b z := by
  rw [terminatingHG_two_neg_nat, terminatingHG_two_neg_nat, Nat.max_comm m n]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (poch (-(n : ℂ)) k)]

@[dlmf 18.21.E2]
theorem krawtchouk_duality (p : ℂ) {N n x : ℕ} (hn : n ≤ N) (hx : x ≤ N) :
    krawtchouk p N n x = krawtchouk p N x n := by
  exact terminatingHG_two_neg_nat_swap n x _ _

@[dlmf 18.21.E2]
theorem meixner_duality (β c : ℂ) (n x : ℕ) : meixner β c n x = meixner β c x n := by
  exact terminatingHG_two_neg_nat_swap n x _ _

@[dlmf 18.21.E2]
theorem charlier_duality (a : ℂ) (n x : ℕ) : charlier a n x = charlier a x n := by
  exact terminatingHG_two_neg_nat_swap n x _ _

@[dlmf 18.22.E10]
theorem hahn_difference_equation {α β : ℂ} (hα : -1 < α.re) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    (x + α + 1) * (x - N) * (hahn α β N n (x + 1) - hahn α β N n x) +
      x * (x - β - N - 1) * (hahn α β N n (x - 1) - hahn α β N n x) =
      n * (n + α + β + 1) * hahn α β N n x := by
  have hpA : ∀ k : ℕ, poch (α + 1) k ≠ 0 := fun k =>
    poch_ne_zero_of_re_pos (by simp; linarith) k
  have hAk : ∀ k : ℕ, α + 1 + k ≠ 0 := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hpN : ∀ k : ℕ, k ≤ N → poch (-(N : ℂ)) k ≠ 0 := fun k hk => by
    rw [poch_neg_coe_nat]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hk).ne')
  set s : ℂ := (n : ℂ) + α + β + 1 with hs
  set u : ℂ := -x with hu
  set cf : ℕ → ℂ := fun k => poch (-(n : ℂ)) k * poch s k / (poch (α + 1) k * poch (-(N : ℂ)) k) /
    k ! with hcf
  set G : ℕ → ℂ := fun k => cf k * ((k - n) * (k + n + α + β + 1) * poch u k) with hG
  set B : ℕ → ℂ := fun k => (u - α - 1) * (u + N) * (poch (u - 1) k - poch u k) +
      u * (u + β + N + 1) * (poch (u + 1) k - poch u k) - n * (n + α + β + 1) * poch u k with hB
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
    rw [poch_succ, poch_succ s, poch_succ (α + 1), poch_succ (-(N : ℂ)), Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have htel : ∀ k : ℕ, k < n → cf (k + 1) * B (k + 1) = G (k + 1) - G k := by
    intro k hk
    simp only [hB, hG]
    rw [hahn_basis_succ α β N u n k]
    have hr := hrec k hk
    push_cast
    linear_combination (poch u k) * hr
  have hkey : ∑ k ∈ Finset.range (n + 1), cf k * B k = 0 := by
    rw [Finset.sum_range_succ']
    rw [Finset.sum_congr rfl fun k hk => htel k (Finset.mem_range.mp hk)]
    rw [Finset.sum_range_sub]
    simp only [hB, hG, hcf, poch_zero, sub_self]
    push_cast
    ring
  unfold hahn terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  rw [show -(x + 1) = u - 1 by rw [hu]; ring, show -(x - 1) = u + 1 by rw [hu]; ring,
    show x + α + 1 = -(u - α - 1) by rw [hu]; ring, show (x : ℂ) - N = -(u + N) by rw [hu]; ring,
    show x - β - N - 1 = -(u + β + N + 1) by rw [hu]; ring, show x = -u by rw [hu]; ring]
  simp only [neg_neg]
  have hfin : ∀ v : ℂ, ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
      (poch ((n : ℂ) + α + β + 1) k * poch v k) / (poch (α + 1) k * poch (-(N : ℂ)) k) /
        (k ! : ℂ) = ∑ k ∈ Finset.range (n + 1), cf k * poch v k := fun v =>
    Finset.sum_congr rfl fun k _ => by simp only [hcf, hs]; ring
  rw [hfin, hfin, hfin]
  clear_value B G cf u s
  have hexp : ∑ k ∈ Finset.range (n + 1), cf k * B k =
      (u - α - 1) * (u + N) * (∑ k ∈ Finset.range (n + 1), cf k * poch (u - 1) k -
        ∑ k ∈ Finset.range (n + 1), cf k * poch u k) +
      u * (u + β + N + 1) * (∑ k ∈ Finset.range (n + 1), cf k * poch (u + 1) k -
        ∑ k ∈ Finset.range (n + 1), cf k * poch u k) -
      n * (n + α + β + 1) * ∑ k ∈ Finset.range (n + 1), cf k * poch u k := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hB]
    ring
  rw [hkey] at hexp
  linear_combination -hexp - (n * ∑ k ∈ Finset.range (n + 1), cf k * poch u k) * hs

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
  unfold meixner terminatingHG
  rw [ordinaryHypergeometric_eq_sum_neg_nat]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, gaussHGCoeff]
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
  unfold krawtchouk terminatingHG
  rw [ordinaryHypergeometric_eq_sum_neg_nat]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, gaussHGCoeff]
  ring

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
theorem poch_neg_succ_sub (x : ℂ) (k : ℕ) :
    poch (-(x + 1)) (k + 1) - poch (-x) (k + 1) = -((k : ℂ) + 1) * poch (-x) k := by
  rw [poch_succ_left, poch_succ, show -(x + 1) + 1 = -x by ring]
  ring

/-- `∏ (t)_{j+1} = (∏ t) ∏ (t+1)_j` over a list of parameters. -/
theorem prod_map_poch_succ (L : List ℂ) (j : ℕ) :
    (L.map (fun t => poch t (j + 1))).prod =
      L.prod * ((L.map (fun t => t + 1)).map (fun t => poch t j)).prod := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih, poch_succ_left]
    ring

/-- The forward difference in `x` of a terminating series whose last numerator parameter is
`-x`: the common step behind 18.22.19–18.22.25. -/
theorem terminatingHG_forward_difference (n : ℕ) (L B : List ℂ) (x z : ℂ) :
    terminatingHG (n + 1) (-((n + 1 : ℕ) : ℂ) :: (L ++ [-(x + 1)])) B z -
      terminatingHG (n + 1) (-((n + 1 : ℕ) : ℂ) :: (L ++ [-x])) B z =
    ((n + 1 : ℕ) : ℂ) * L.prod / B.prod * z *
      terminatingHG n (-(n : ℂ) :: (L.map (fun t => t + 1) ++ [-x])) (B.map (fun t => t + 1)) z := by
  unfold terminatingHG
  rw [← Finset.sum_sub_distrib, Finset.sum_range_succ', Finset.mul_sum]
  have h0 : (((-((n + 1 : ℕ) : ℂ) :: (L ++ [-(x + 1)])).map (fun t => poch t 0)).prod /
        (B.map (fun t => poch t 0)).prod * z ^ 0 / ((0 : ℕ).factorial : ℂ) -
      ((-((n + 1 : ℕ) : ℂ) :: (L ++ [-x])).map (fun t => poch t 0)).prod /
        (B.map (fun t => poch t 0)).prod * z ^ 0 / ((0 : ℕ).factorial : ℂ)) = 0 := by
    simp [poch_zero]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast j.succ_ne_zero
  simp only [List.map_cons, List.map_append, List.map_nil, List.prod_cons, List.prod_append,
    List.prod_nil, mul_one]
  rw [prod_map_poch_succ L j, prod_map_poch_succ B j, poch_succ_left (-((n + 1 : ℕ) : ℂ)),
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring, Nat.factorial_succ, pow_succ]
  push_cast
  have hd := poch_neg_succ_sub x j
  have hinv : ((j : ℂ) + 1) * ((j : ℂ) + 1)⁻¹ = 1 := mul_inv_cancel₀ hj
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination
    (((n : ℂ) + 1) * (poch (-(n : ℂ)) j * L.prod *
      ((L.map (fun t => t + 1)).map (fun t => poch t j)).prod * (B.prod)⁻¹ *
      (((B.map (fun t => t + 1)).map (fun t => poch t j)).prod)⁻¹ * z ^ j * z *
      ((j.factorial : ℂ))⁻¹) * poch (-x) j) * hinv -
    (((n : ℂ) + 1) * (poch (-(n : ℂ)) j * L.prod *
      ((L.map (fun t => t + 1)).map (fun t => poch t j)).prod * (B.prod)⁻¹ *
      (((B.map (fun t => t + 1)).map (fun t => poch t j)).prod)⁻¹ * z ^ j * z *
      ((j.factorial : ℂ))⁻¹) * ((j : ℂ) + 1)⁻¹) * hd

/-- `(-n)_{n+1} = 0`. -/
theorem poch_neg_nat_succ (n : ℕ) : poch (-(n : ℂ)) (n + 1) = 0 := by
  rw [poch_succ]
  simp

/-- The difference of a terminating series in its truncation parameter: the companion of
`terminatingHG_forward_difference` for the first numerator parameter. -/
theorem terminatingHG_first_difference (n : ℕ) (L B : List ℂ) (z : ℂ) :
    terminatingHG (n + 1) (-((n + 1 : ℕ) : ℂ) :: L) B z - terminatingHG n (-(n : ℂ) :: L) B z =
      -(L.prod / B.prod * z) * terminatingHG n (-(n : ℂ) :: L.map (fun t => t + 1)) (B.map (fun t => t + 1)) z := by
  unfold terminatingHG
  have hext : ∑ k ∈ Finset.range (n + 1), ((-(n : ℂ) :: L).map (fun t => poch t k)).prod /
        (B.map (fun t => poch t k)).prod * z ^ k / (k.factorial : ℂ) =
      ∑ k ∈ Finset.range (n + 1 + 1), ((-(n : ℂ) :: L).map (fun t => poch t k)).prod /
        (B.map (fun t => poch t k)).prod * z ^ k / (k.factorial : ℂ) := by
    rw [Finset.sum_range_succ _ (n + 1)]
    simp [poch_neg_nat_succ]
  rw [hext, ← Finset.sum_sub_distrib, Finset.sum_range_succ', Finset.mul_sum]
  simp only [List.map_cons, List.prod_cons]
  have h0 : (poch (-((n + 1 : ℕ) : ℂ)) 0 * (L.map (fun t => poch t 0)).prod /
        (B.map (fun t => poch t 0)).prod * z ^ 0 / ((0 : ℕ).factorial : ℂ) -
      poch (-(n : ℂ)) 0 * (L.map (fun t => poch t 0)).prod /
        (B.map (fun t => poch t 0)).prod * z ^ 0 / ((0 : ℕ).factorial : ℂ)) = 0 := by
    simp [poch_zero]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast j.succ_ne_zero
  rw [prod_map_poch_succ L j, prod_map_poch_succ B j, Nat.factorial_succ, pow_succ]
  have hd := poch_neg_succ_sub (n : ℂ) j
  push_cast
  have hinv : ((j : ℂ) + 1) * ((j : ℂ) + 1)⁻¹ = 1 := mul_inv_cancel₀ hj
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination
    (-(L.prod * ((L.map (fun t => t + 1)).map (fun t => poch t j)).prod * (B.prod)⁻¹ *
      (((B.map (fun t => t + 1)).map (fun t => poch t j)).prod)⁻¹ * z ^ j * z *
      ((j.factorial : ℂ))⁻¹) * poch (-(n : ℂ)) j) * hinv +
    ((L.prod * ((L.map (fun t => t + 1)).map (fun t => poch t j)).prod * (B.prod)⁻¹ *
      (((B.map (fun t => t + 1)).map (fun t => poch t j)).prod)⁻¹ * z ^ j * z *
      ((j.factorial : ℂ))⁻¹) * ((j : ℂ) + 1)⁻¹) * hd

/-- `C_{n+1}(x) - C_n(x) = -(x/a) C_n(x - 1)`, the Charlier companion of 18.22.25 in `n`. -/
theorem charlier_first_difference (a : ℂ) (n : ℕ) (x : ℂ) :
    charlier a (n + 1) x - charlier a n x = -(x / a) * charlier a n (x - 1) := by
  unfold charlier
  have h := terminatingHG_first_difference n [-x] [] (-a⁻¹)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    show -x + 1 = -(x - 1) by ring] at h
  rw [h]
  ring

@[dlmf 18.22.E19]
theorem hahn_forward_difference {α β : ℂ} (hα : -1 < α.re) {N n : ℕ} (hn : n + 1 ≤ N + 1) (x : ℂ) :
    hahn α β (N + 1) (n + 1) (x + 1) - hahn α β (N + 1) (n + 1) x =
      -((n + 1) * (n + α + β + 2)) / ((α + 1) * (N + 1)) * hahn (α + 1) (β + 1) N n x := by
  unfold hahn
  have h := terminatingHG_forward_difference n [((n + 1 : ℕ) : ℂ) + α + β + 1]
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

@[dlmf 18.22.E21]
theorem krawtchouk_forward_difference {p : ℂ} (hp : p ≠ 0) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    krawtchouk p (N + 1) (n + 1) (x + 1) - krawtchouk p (N + 1) (n + 1) x =
      -(n + 1) / (p * (N + 1)) * krawtchouk p N n x := by
  unfold krawtchouk
  have h := terminatingHG_forward_difference n [] [-((N + 1 : ℕ) : ℂ)] x p⁻¹
  simp only [List.nil_append, List.map_nil, List.prod_nil, List.map_cons, List.prod_cons,
    show -((N + 1 : ℕ) : ℂ) + 1 = -(N : ℂ) by push_cast; ring] at h
  rw [h]
  have hN : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast N.succ_ne_zero
  push_cast
  field_simp

@[dlmf 18.22.E23]
theorem meixner_forward_difference {β c : ℂ} (hβ : 0 < β.re) (hc : c ≠ 0) (n : ℕ) (x : ℂ) :
    meixner β c (n + 1) (x + 1) - meixner β c (n + 1) x =
      -(n + 1) * (1 - c) / (β * c) * meixner (β + 1) c n x := by
  unfold meixner
  have h := terminatingHG_forward_difference n [] [β] x (1 - c⁻¹)
  simp only [List.nil_append, List.map_nil, List.prod_nil, List.map_cons, List.prod_cons] at h
  rw [h]
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0] at hβ
    simp at hβ
  push_cast
  field_simp
  ring

@[dlmf 18.22.E25]
theorem charlier_forward_difference {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    charlier a (n + 1) (x + 1) - charlier a (n + 1) x = -(n + 1) / a * charlier a n x := by
  unfold charlier
  have h := terminatingHG_forward_difference n [] [] x (-a⁻¹)
  simp only [List.nil_append, List.map_nil, List.prod_nil] at h
  rw [h]
  push_cast
  field_simp

@[dlmf 18.22.T2]
theorem charlier_difference_equation {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    a * (charlier a n (x + 1) - charlier a n x) +
      x * (charlier a n (x - 1) - charlier a n x) + n * charlier a n x = 0 := by
  cases n with
  | zero => simp [charlier, terminatingHG, poch_zero]
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

@[dlmf 18.22.E8]
theorem meixnerPollaczek_recurrence {lam : ℂ} (hlam : 0 < lam.re) (phi : ℂ) (n : ℕ) (x : ℂ) :
    (n + 2 : ℂ) * meixnerPollaczek lam phi (n + 2) x =
      2 * (x * sin phi + (n + lam + 1) * cos phi) * meixnerPollaczek lam phi (n + 1) x -
      (n + 2 * lam) * meixnerPollaczek lam phi n x := by
  have hc : ∀ k : ℕ, 2 * lam ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hcont :=
    Hypergeometric.contiguous_a_neg_nat hc n (b := lam + I * x) (1 - cexp (-2 * I * phi))
  unfold meixnerPollaczek
  rw [terminatingHG_eq_ordinaryHypergeometric, terminatingHG_eq_ordinaryHypergeometric,
    terminatingHG_eq_ordinaryHypergeometric]
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
  have hp2 : poch (2 * lam) (n + 2) = poch (2 * lam) n * (2 * lam + n) * (2 * lam + (n + 1)) := by
    rw [poch_succ, poch_succ]; push_cast; ring
  have hp1 : poch (2 * lam) (n + 1) = poch (2 * lam) n * (2 * lam + n) := by
    rw [poch_succ]
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
  linear_combination (poch (2 * lam) n * (2 * lam + n) * E) * hcont

/-- The Meixner–Pollaczek polynomial of degree one. -/
theorem meixnerPollaczek_one {lam : ℂ} (hlam : lam ≠ 0) (phi x : ℂ) :
    meixnerPollaczek lam phi 1 x = 2 * (x * sin phi + lam * cos phi) := by
  unfold meixnerPollaczek terminatingHG
  set u := cexp (I * phi) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  have e2 : cexp (-2 * I * phi) = (u ^ 2)⁻¹ := by
    rw [hu, ← Complex.exp_nat_mul, ← Complex.exp_neg]; congr 1; push_cast; ring
  have hcos : cos phi = (u + u⁻¹) / 2 := by
    rw [Complex.cos, hu, ← Complex.exp_neg]; congr 2 <;> ring_nf
  have hsin : sin phi = (u⁻¹ - u) * I / 2 := by
    rw [Complex.sin, hu, ← Complex.exp_neg]; congr 3 <;> ring_nf
  rw [e2]
  simp [Finset.sum_range_succ, poch_zero, poch_one, hcos, hsin, ← hu]
  field_simp
  ring_nf

@[dlmf 18.22.E29]
theorem meixnerPollaczek_central_difference {lam : ℂ} (hlam : 0 < lam.re) (phi : ℂ) (n : ℕ) (x : ℂ) :
    (meixnerPollaczek lam phi (n + 1) (x + I / 2) - meixnerPollaczek lam phi (n + 1) (x - I / 2)) / I =
      2 * sin phi * meixnerPollaczek (lam + 1 / 2) phi n x := by
  have h2 : 0 < (2 * lam).re := by simp; linarith
  have h2l : 2 * lam ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have hl0 : lam ≠ 0 := fun h => by rw [h] at hlam; simp at hlam
  have hp : ∀ k : ℕ, poch (2 * lam + 1) k ≠ 0 := fun k =>
    poch_ne_zero_of_re_pos (by simp; linarith) k
  unfold meixnerPollaczek terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [poch_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, sub_self, add_zero,
    pow_zero]
  rw [show lam + I * (x + I / 2) = (lam + I * x) - 1 / 2 by linear_combination (1 / 2 : ℂ) * I_sq,
    show lam + I * (x - I / 2) = (lam + I * x) + 1 / 2 by linear_combination (-1 / 2 : ℂ) * I_sq]
  rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have key := poch_half_sub (lam + I * x) k
  rw [← sub_div, ← sub_mul, ← sub_div, ← mul_sub, key]
  have hS := exp_mul_one_sub_exp phi
  rw [poch_succ_left (2 * lam), poch_succ_left (2 * lam) k, poch_succ_left (-((n + 1 : ℕ) : ℂ)),
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
theorem sum_choose_mul_poch_neg_nat_mul_pow {N k : ℕ} (hk : k ≤ N) (z w : ℂ) :
    ∑ n ∈ Finset.range (N + 1), (N.choose n : ℂ) * poch (-(n : ℂ)) k * z ^ n * w ^ (N - n) =
      poch (-(N : ℂ)) k * z ^ k * (z + w) ^ (N - k) := by
  rw [show N + 1 = k + (N - k + 1) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero fun n hn => by
    rw [poch_neg_nat_eq_zero (by simpa using hn)]; simp, zero_add]
  rw [add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ N - k := by simp at hm; omega
  rw [poch_neg_coe_nat, poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose, pow_add, show N - (k + m) = N - k - m by omega]
  have hc := Nat.choose_mul (n := N) (k := k + m) (s := k) (by omega)
  rw [show k + m - k = m by omega] at hc
  have hc' : (N.choose (k + m) : ℂ) * ((k + m).choose k) = N.choose k * (N - k).choose m := by
    exact_mod_cast hc
  push_cast
  linear_combination (-1 : ℂ) ^ k * k ! * z ^ k * z ^ m * w ^ (N - k - m) * hc'

/-- `∑ₙ C(N,n) (-n)ₖ zⁿ = (-N)ₖ zᵏ (1+z)^{N-k}` for `k ≤ N`. -/
theorem sum_choose_mul_poch_neg_nat {N k : ℕ} (hk : k ≤ N) (z : ℂ) :
    ∑ n ∈ Finset.range (N + 1), (N.choose n : ℂ) * poch (-(n : ℂ)) k * z ^ n =
      poch (-(N : ℂ)) k * z ^ k * (1 + z) ^ (N - k) := by
  simpa [add_comm z] using sum_choose_mul_poch_neg_nat_mul_pow hk z 1

@[dlmf 18.23.E3]
theorem krawtchouk_generating_function {p : ℂ} (hp : p ≠ 0) {N x : ℕ} (hx : x ≤ N) (z : ℂ) :
    ∑ n ∈ Finset.range (N + 1), (N.choose n : ℂ) * krawtchouk p N n x * z ^ n =
      (1 - (1 - p) / p * z) ^ x * (1 + z) ^ (N - x) := by
  unfold krawtchouk
  simp_rw [terminatingHG_two_neg_nat_swap _ x, terminatingHG, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ k ∈ Finset.range (x + 1), ∑ n ∈ Finset.range (N + 1),
      (N.choose n : ℂ) * ((([-(x : ℂ), -(n : ℂ)].map fun t => poch t k).prod /
        ([-(N : ℂ)].map fun t => poch t k).prod * p⁻¹ ^ k / k !)) * z ^ n =
      (1 + z) ^ (N - x) * ((x.choose k : ℂ) * (-(z / p)) ^ k * (1 + z) ^ (x - k)) := by
    intro k hk
    have hkx : k ≤ x := by simp at hk; omega
    have hN : poch (-(N : ℂ)) k ≠ 0 := by
      rw [poch_neg_coe_nat]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr (by omega)).ne')
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have hs := sum_choose_mul_poch_neg_nat (show k ≤ N by omega) z
    rw [Finset.sum_congr rfl (g := fun n : ℕ => (poch (-(x : ℂ)) k / poch (-(N : ℂ)) k *
      p⁻¹ ^ k / k !) * ((N.choose n : ℂ) * poch (-(n : ℂ)) k * z ^ n)) (fun n _ => by ring),
      ← Finset.mul_sum, hs, poch_neg_coe_nat x, Nat.descFactorial_eq_factorial_mul_choose,
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
theorem hasSum_poch_mul_poch_neg_nat {β z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    HasSum (fun n : ℕ => poch β n / n ! * poch (-(n : ℂ)) k * z ^ n)
      (poch β k * (-z) ^ k * (1 - z) ^ (-(β + k))) := by
  have hb := (hasSum_poch_div_factorial (β := β + k) hz).mul_left (poch β k * (-z) ^ k)
  have h0 : ∑ i ∈ Finset.range k, poch β i / i ! * poch (-(i : ℂ)) k * z ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [poch_neg_nat_eq_zero (by simpa using hi)]; simp
  have key := (hasSum_nat_add_iff (f := fun n : ℕ => poch β n / n ! * poch (-(n : ℂ)) k * z ^ n)
    k (g := poch β k * (-z) ^ k * (1 - z) ^ (-(β + k)))).mp ?_
  · rwa [h0, add_zero] at key
  refine hb.congr_fun fun n => ?_
  have hn' : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hnk : ((n + k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd : ((n + k).descFactorial k : ℂ) * n ! = (n + k) ! := by
    have := Nat.factorial_mul_descFactorial (show k ≤ n + k by omega)
    rw [show n + k - k = n by omega] at this
    exact_mod_cast (mul_comm _ _).trans this
  rw [poch_neg_coe_nat, add_comm n k, poch_add, neg_pow, pow_add, add_comm k n]
  field_simp
  linear_combination (-1) ^ k * poch β k * poch (β + k) n * z ^ n * z ^ k * hd

@[dlmf 18.23.E4]
theorem meixner_generating_function {β c : ℂ} (hβ : 0 < β.re) (hc : c ≠ 0) (x : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => poch β n / n.factorial * meixner β c n x * z ^ n)
      ((1 - z / c) ^ x * (1 - z) ^ (-(x : ℂ) - β)) := by
  have hβk : ∀ k, poch β k ≠ 0 := poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hβ)
  have h1z : (1 : ℂ) - z ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this, norm_one] at hz
    exact lt_irrefl _ hz
  set u : ℂ := 1 - c⁻¹
  unfold meixner
  simp_rw [terminatingHG_two_neg_nat_swap _ x, terminatingHG, Finset.mul_sum, Finset.sum_mul]
  have h := hasSum_sum (s := Finset.range (x + 1)) (fun k _ =>
    (hasSum_poch_mul_poch_neg_nat (β := β) hz k).mul_left
      (poch (-(x : ℂ)) k / poch β k * u ^ k / k !))
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
    have hbin := sum_poch_neg_nat_div_factorial_mul_pow x (-(u * z) / (1 - z))
    rw [show (1 : ℂ) - -(u * z) / (1 - z) = (1 - z / c) / (1 - z) by
      simp only [u]; field_simp; ring, div_pow] at hbin
    have hterm : ∀ k ∈ Finset.range (x + 1), poch (-(x : ℂ)) k / poch β k * u ^ k / k ! *
        (poch β k * (-z) ^ k * (1 - z) ^ (-(β + k))) =
        (1 - z) ^ (-β) * (poch (-(x : ℂ)) k / k ! * (-(u * z) / (1 - z)) ^ k) := by
      intro k _
      rw [hsplit, div_pow]
      have := hβk k
      field_simp
      rw [show -(z * u) = u * -z by ring, mul_pow]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hbin, hx]
    field_simp

/-- `∑ₙ (-n)ₖ wⁿ / n! = (-w)ᵏ eʷ`. -/
theorem hasSum_poch_neg_nat_div_factorial (k : ℕ) (w : ℂ) :
    HasSum (fun n : ℕ => poch (-(n : ℂ)) k / n ! * w ^ n) ((-w) ^ k * exp w) := by
  have he : HasSum (fun n : ℕ => w ^ n / n !) (exp w) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp w
  have h0 : ∑ i ∈ Finset.range k, poch (-(i : ℂ)) k / i ! * w ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [poch_neg_nat_eq_zero (by simpa using hi)]; simp
  have key := (hasSum_nat_add_iff (f := fun n : ℕ => poch (-(n : ℂ)) k / n ! * w ^ n) k
    (g := (-w) ^ k * exp w)).mp ?_
  · rwa [h0, add_zero] at key
  refine (he.mul_left ((-w) ^ k)).congr_fun fun n => ?_
  have hn : ((n + k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn' : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd : ((n + k).descFactorial k : ℂ) * n ! = (n + k) ! := by
    have := Nat.factorial_mul_descFactorial (show k ≤ n + k by omega)
    rw [show n + k - k = n by omega] at this
    exact_mod_cast (mul_comm _ _).trans this
  rw [poch_neg_coe_nat, neg_pow, pow_add]
  field_simp
  linear_combination (-1) ^ k * w ^ n * w ^ k * hd

@[dlmf 18.23.E5]
theorem charlier_generating_function (a : ℂ) (x : ℕ) (z : ℂ) :
    HasSum (fun n : ℕ => charlier a n x / n.factorial * z ^ n) (exp z * (1 - z / a) ^ x) := by
  unfold charlier
  simp_rw [terminatingHG_two_neg_nat_swap _ x, terminatingHG, Finset.sum_div, Finset.sum_mul]
  have h := hasSum_sum (s := Finset.range (x + 1)) (fun k _ =>
    (hasSum_poch_neg_nat_div_factorial k z).mul_left (poch (-(x : ℂ)) k * (-a⁻¹) ^ k / k !))
  convert h using 1
  · funext n
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
    ring
  · rw [← sum_poch_neg_nat_div_factorial_mul_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show z / a = (-a⁻¹) * (-z) by ring, mul_pow]
    ring

/-- The Meixner–Pollaczek polynomial of degree zero. -/
theorem meixnerPollaczek_zero (lam phi x : ℂ) : meixnerPollaczek lam phi 0 x = 1 := by
  simp [meixnerPollaczek, terminatingHG, poch_zero]

/-- `e^{iφ} + e^{-iφ} = 2 cos φ` and `e^{-iφ} - e^{iφ} = -2 i sin φ`, in the form used below. -/
theorem exp_I_mul_add_recip (phi : ℂ) :
    exp (I * phi) + (exp (I * phi))⁻¹ = 2 * cos phi ∧
      exp (I * phi) - (exp (I * phi))⁻¹ = 2 * I * sin phi := by
  rw [← Complex.exp_neg, Complex.cos, Complex.sin]
  constructor
  · ring_nf
  · ring_nf; rw [I_sq]; ring

@[dlmf 18.23.E7]
theorem meixnerPollaczek_generating_function {lam : ℂ} (hlam : 0 < lam.re) (phi x : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => meixnerPollaczek lam phi n x * z ^ n)
      ((1 - exp (I * phi) * z) ^ (-lam + I * x) * (1 - exp (-I * phi) * z) ^ (-lam - I * x)) := by
  set u := exp (I * phi) with hu
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hu1 : ‖u‖ = 1 := by rw [hu, mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hlam0 : lam ≠ 0 := fun h => by rw [h, Complex.zero_re] at hlam; exact lt_irrefl _ hlam
  obtain ⟨hcos, hsin⟩ := exp_I_mul_add_recip (phi : ℂ)
  have hcoeff : ∀ n, meixnerPollaczek lam phi n x =
      PowerSeries.coeff n (binomProductSeries (lam - I * x) (lam + I * x) u) := by
    refine eq_coeff_binomProductSeries hu0 (meixnerPollaczek_zero _ _ _) ?_ ?_
    · rw [meixnerPollaczek_one hlam0]
      linear_combination (-lam) * hcos + (I * x) * hsin + (2 * x * sin (phi : ℂ)) * I_sq
    · intro n
      rw [meixnerPollaczek_recurrence hlam]
      linear_combination (-(n + 1 + lam : ℂ) * meixnerPollaczek lam phi (n + 1) x) * hcos +
        (I * x * meixnerPollaczek lam phi (n + 1) x) * hsin +
        (2 * x * sin (phi : ℂ) * meixnerPollaczek lam phi (n + 1) x) * I_sq
  have h1 : ‖u * z‖ < 1 := by rwa [norm_mul, hu1, one_mul]
  have h2 : ‖u⁻¹ * z‖ < 1 := by rwa [norm_mul, norm_inv, hu1, inv_one, one_mul]
  have h := hasSum_coeff_binomProductSeries_mul_pow (lam - I * x) (lam + I * x) h1 h2
  rw [show u⁻¹ = exp (-I * phi) by rw [hu, ← Complex.exp_neg]; ring_nf,
    show -(lam - I * x) = -lam + I * x by ring, show -(lam + I * x) = -lam - I * x by ring] at h
  simpa only [hcoeff] using h

/-- Limits propagate through a three-term recurrence whose coefficients converge. -/
theorem tendsto_of_three_term {ι : Type*} {l : Filter ι} {f : ℕ → ι → ℂ} {g : ℕ → ℂ}
    {A B : ℕ → ι → ℂ} {A' B' : ℕ → ℂ}
    (h0 : Tendsto (f 0) l (𝓝 (g 0))) (h1 : Tendsto (f 1) l (𝓝 (g 1)))
    (hA : ∀ n, Tendsto (A n) l (𝓝 (A' n))) (hB : ∀ n, Tendsto (B n) l (𝓝 (B' n)))
    (hf : ∀ n, ∀ᶠ t in l, f (n + 2) t = A n t * f (n + 1) t + B n t * f n t)
    (hg : ∀ n, g (n + 2) = A' n * g (n + 1) + B' n * g n) (n : ℕ) :
    Tendsto (f n) l (𝓝 (g n)) := by
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih0 ih1 =>
    rw [hg n]
    exact (((hA n).mul ih1).add ((hB n).mul ih0)).congr' (by
      filter_upwards [hf n] with t ht
      exact ht.symm)

/-- `c / a → 0` for complex `c` as the real `a → ∞`. -/
theorem tendsto_const_div_ofReal_atTop (c : ℂ) :
    Tendsto (fun a : ℝ => c / (a : ℂ)) atTop (𝓝 0) := by
  have := (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  rw [ofReal_zero] at this
  simpa [div_eq_mul_inv] using this.const_mul c

/-- `(c + s t)_k / t^k → s^k` as the real `t → ∞`. -/
theorem tendsto_poch_add_mul_div_pow (c s : ℂ) (k : ℕ) :
    Tendsto (fun t : ℝ => poch (c + s * t) k / (t : ℂ) ^ k) atTop (𝓝 (s ^ k)) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have h1 : Tendsto (fun t : ℝ => (c + k) / (t : ℂ) + s) atTop (𝓝 s) := by
      simpa using (tendsto_const_div_ofReal_atTop (c + k)).add_const s
    refine ((ih.mul h1).congr' ?_).trans (by rw [pow_succ])
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [poch_succ, pow_succ]
    field_simp
    ring

@[dlmf 18.21.E3]
theorem hahn_limit_krawtchouk {p : ℝ} (hp : 0 < p) (N n : ℕ) (x : ℂ) :
    Tendsto (fun t : ℝ => hahn (p * t) ((1 - p) * t) N n x) atTop (𝓝 (krawtchouk p N n x)) := by
  unfold hahn krawtchouk terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hpt : Tendsto (fun t : ℝ => p * t) atTop atTop := tendsto_id.const_mul_atTop hp
  have h1 := tendsto_poch_add_div_pow ((n : ℂ) + 1) k
  have h2 := ((tendsto_poch_add_div_pow 1 k).comp hpt).inv₀ one_ne_zero
  rw [inv_one] at h2
  have := (h1.mul h2).const_mul
    (poch (-(n : ℂ)) k * poch (-x) k / poch (-(N : ℂ)) k / k.factorial * ((p : ℂ)⁻¹) ^ k)
  rw [mul_one, mul_one] at this
  rw [show poch (-(n : ℂ)) k * poch (-x) k / poch (-(N : ℂ)) k * (p : ℂ)⁻¹ ^ k /
      (k.factorial : ℂ) = poch (-(n : ℂ)) k * poch (-x) k / poch (-(N : ℂ)) k /
      k.factorial * ((p : ℂ)⁻¹) ^ k by ring]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hp' : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  simp only [Function.comp_apply, ofReal_mul]
  have e1 : (n : ℂ) + (p * t) + ((1 - p) * t) + 1 = (n + 1) + t := by ring
  have e2 : (p : ℂ) * t + 1 = 1 + p * t := by ring
  rw [e1, e2, mul_pow, inv_pow]
  field_simp
  ring

@[dlmf 18.21.E5]
theorem hahn_limit_jacobi {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (x : ℂ) :
    Tendsto (fun N : ℕ => hahn α β N n (N * x)) atTop (𝓝 (jacobiPolyP α β n (1 - 2 * x) / jacobiPolyP α β n 1)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hP1 : poch ((α : ℂ) + 1) n / (n ! : ℂ) ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat hα' n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have hJ : jacobiPolyP α β n (1 - 2 * x) / jacobiPolyP α β n 1 =
      ∑ k ∈ Finset.range (n + 1), gaussHGCoeff (-(n : ℂ)) (n + α + β + 1) (α + 1) k * x ^ k := by
    unfold jacobiPolyP
    rw [show (1 - (1 - 2 * x)) / 2 = x by ring, sub_self, zero_div,
      ordinaryHypergeometric_zero, mul_one, mul_div_cancel_left₀ _ hP1,
      ordinaryHypergeometric_eq_sum_neg_nat]
  rw [hJ]
  unfold hahn terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have h1 := (tendsto_poch_add_mul_div_pow 0 (-x) k).comp hnat
  have h2 := (tendsto_poch_add_mul_div_pow 0 (-1) k).comp hnat
  have hneg : ((-1 : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 := (h1.div h2 hneg).const_mul (gaussHGCoeff (-(n : ℂ)) (n + α + β + 1) (α + 1) k)
  rw [show (-x) ^ k / (-1 : ℂ) ^ k = x ^ k by rw [neg_pow x, mul_div_cancel_left₀ _ hneg]] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Pi.div_apply, Function.comp_apply, zero_add, ofReal_natCast]
  rw [show -1 * (N : ℂ) = -(N : ℂ) by ring, show -x * (N : ℂ) = -(N * x) by ring]
  have hNk : ((N : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN.ne')
  unfold gaussHGCoeff
  by_cases hp : poch (-(N : ℂ)) k = 0
  · simp [hp]
  · field_simp

@[dlmf 18.21.E6]
theorem krawtchouk_limit_charlier {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    Tendsto (fun N : ℕ => krawtchouk (a / N) N n x) atTop (𝓝 (charlier a n x)) := by
  unfold krawtchouk charlier terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hlim := (tendsto_poch_neg_div_pow k).inv₀ one_ne_zero
  rw [inv_one] at hlim
  have := hlim.const_mul (poch (-(n : ℂ)) k * poch (-x) k / k.factorial * (-a⁻¹) ^ k)
  rw [mul_one] at this
  rw [show poch (-(n : ℂ)) k * poch (-x) k / 1 * (-a⁻¹) ^ k / (k.factorial : ℂ) =
      poch (-(n : ℂ)) k * poch (-x) k / k.factorial * (-a⁻¹) ^ k by ring]
  refine this.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [inv_div] at hlim ⊢
  have e : (-a⁻¹) ^ k * (-(N : ℂ)) ^ k = ((N : ℂ) / a) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  linear_combination (poch (-(n : ℂ)) k * poch (-x) k / k.factorial / poch (-(N : ℂ)) k) * e

@[dlmf 18.21.E7]
theorem meixner_limit_charlier {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℂ) :
    Tendsto (fun b : ℝ => meixner b (a / (a + b)) n x) atTop (𝓝 (charlier a n x)) := by
  unfold meixner charlier terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hlim := (tendsto_poch_add_div_pow 0 k).inv₀ one_ne_zero
  rw [inv_one] at hlim
  simp only [inv_div, zero_add] at hlim
  have := hlim.const_mul (poch (-(n : ℂ)) k * poch (-x) k / k.factorial * (-(a : ℂ)⁻¹) ^ k)
  rw [mul_one] at this
  rw [show poch (-(n : ℂ)) k * poch (-x) k / 1 * (-(a : ℂ)⁻¹) ^ k / (k.factorial : ℂ) =
      poch (-(n : ℂ)) k * poch (-x) k / k.factorial * (-(a : ℂ)⁻¹) ^ k by ring]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hab : (a : ℂ) + b ≠ 0 := by exact_mod_cast (add_pos ha hb).ne'
  have e : (-(a : ℂ)⁻¹) ^ k * (b : ℂ) ^ k = (1 - ((a : ℂ) / (a + b))⁻¹) ^ k := by
    rw [← mul_pow]; congr 1; field_simp; ring
  linear_combination (poch (-(n : ℂ)) k * poch (-x) k / k.factorial / poch (b : ℂ) k) * e

/-- Charlier polynomials as polynomials in `x`. -/
def charlierPoly (a : ℂ) (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (poch (-(n : ℂ)) k * (-a⁻¹) ^ k / k.factorial) *
    (ascPochhammer ℂ k).comp (-X)

/-- Evaluation of `charlierPoly` is the Charlier polynomial. -/
theorem eval_charlierPoly (a : ℂ) (n : ℕ) (x : ℂ) : (charlierPoly a n).eval x = charlier a n x := by
  simp only [charlierPoly, charlier, terminatingHG, eval_finsetSum, eval_mul, eval_C, eval_comp,
    eval_neg, eval_X, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [poch]; ring

/-- The three-term recurrence of the Charlier polynomials in the degree. -/
theorem charlier_recurrence {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    a * charlier a (n + 2) x =
      (n + 1 + a - x) * charlier a (n + 1) x - (n + 1) * charlier a n x := by
  -- integer points, from the difference equation and duality
  have hint : ∀ m : ℕ, a * charlier a (n + 2) m =
      (n + 1 + a - m) * charlier a (n + 1) m - (n + 1) * charlier a n m := by
    intro m
    have h := charlier_difference_equation ha m ((n + 1 : ℕ) : ℂ)
    rw [show ((n + 1 : ℕ) : ℂ) + 1 = ((n + 2 : ℕ) : ℂ) by push_cast; ring,
      show ((n + 1 : ℕ) : ℂ) - 1 = ((n : ℕ) : ℂ) by push_cast; ring,
      charlier_duality a m (n + 2), charlier_duality a m (n + 1), charlier_duality a m n] at h
    push_cast at h
    linear_combination h
  -- polynomial identity
  have hpoly : C a * charlierPoly a (n + 2) =
      (C (n + 1 + a) - X) * charlierPoly a (n + 1) - C ((n : ℂ) + 1) * charlierPoly a n := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (m : ℂ))
      Nat.cast_injective fun m => ?_
    simp only [Set.mem_ofPred_eq, eval_mul, eval_sub, eval_C, eval_X, eval_charlierPoly]
    rw [hint m]
  have := congrArg (eval x) hpoly
  simp only [eval_mul, eval_sub, eval_C, eval_X, eval_charlierPoly] at this
  rw [this]


@[dlmf 18.21.E9]
theorem charlier_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => (Real.sqrt (2 * a) : ℂ) ^ n * charlier a n ((Real.sqrt (2 * a) : ℂ) * x + a)) atTop (𝓝 ((-1 : ℂ) ^ n * aeval x (hermitePolyH n))) := by
  set f : ℕ → ℝ → ℂ := fun n a =>
    (Real.sqrt (2 * a) : ℂ) ^ n * charlier a n ((Real.sqrt (2 * a) : ℂ) * x + a) with hf
  -- the scaled recurrence coefficient `√(2a)/a`
  have hs : Tendsto (fun a : ℝ => ((Real.sqrt (2 * a) / a : ℝ) : ℂ)) atTop (𝓝 0) := by
    have : Tendsto (fun a : ℝ => Real.sqrt 2 * (Real.sqrt a)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop)).const_mul (Real.sqrt 2)
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp]
    refine Complex.continuous_ofReal.continuousAt.tendsto.comp (this.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with a ha
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_div_assoc]
    congr 1
    have hsa : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha
    field_simp
    rw [Real.sq_sqrt ha.le]
  refine tendsto_of_three_term (f := f) (g := fun n => (-1 : ℂ) ^ n * aeval x (hermitePolyH n))
    (A := fun n a => (n + 1 : ℂ) * ((Real.sqrt (2 * a) / a : ℝ) : ℂ) - 2 * x)
    (B := fun n _ => -2 * (n + 1 : ℂ)) (A' := fun _ => -2 * x) (B' := fun n => -2 * (n + 1 : ℂ))
    ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp [hf, charlier, terminatingHG, poch_zero]
  · have h1 : (aeval x (hermitePolyH 1) : ℂ) = 2 * x := by simp [hermitePolyH_succ, map_ofNat]
    simp only [pow_one, h1]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with a ha
    have hsq : ((Real.sqrt (2 * a) : ℝ) : ℂ) ^ 2 = 2 * a := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    simp only [hf, charlier, terminatingHG, Finset.sum_range_succ, Finset.sum_range_zero,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, poch_zero, poch_one, pow_one]
    field_simp
    linear_combination x * hsq
  · intro n
    simpa using (hs.const_mul ((n : ℂ) + 1)).sub_const (2 * x)
  · intro n; exact tendsto_const_nhds
  · intro n
    filter_upwards [eventually_gt_atTop 0] with a ha
    have hsq : ((Real.sqrt (2 * a) : ℝ) : ℂ) ^ 2 = 2 * a := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hrec := charlier_recurrence ha0 n ((Real.sqrt (2 * a) : ℂ) * x + a)
    simp only [hf]
    set S : ℂ := ((Real.sqrt (2 * a) : ℝ) : ℂ)
    push_cast
    rw [show S ^ (n + 2) = S ^ n * S ^ 2 by ring, show S ^ (n + 1) = S ^ n * S by ring]
    field_simp
    linear_combination (S ^ n * S ^ 2) * hrec -
      (S * S ^ n * x * charlier (↑a) (n + 1) (S * x + ↑a) +
        S ^ n * (n + 1) * charlier (↑a) n (S * x + ↑a)) * hsq
  · intro n
    rw [aeval_hermitePolyH_succ_succ]
    ring


@[dlmf 18.21.E4]
theorem hahn_limit_meixner {β c : ℝ} (hc : 0 < c) (hc1 : c < 1) (n : ℕ) (x : ℂ) :
    Tendsto (fun N : ℕ => hahn (β - 1) (N * (c⁻¹ - 1)) N n x) atTop (𝓝 (meixner β c n x)) := by
  unfold hahn meixner terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  set d : ℝ := c⁻¹ - 1 with hd
  have hd0 : 0 < d := by rw [hd, sub_pos]; exact one_lt_inv₀ hc |>.mpr hc1
  have hNd : Tendsto (fun N : ℕ => (N : ℝ) * d) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hd0
  have h1 := (tendsto_poch_add_div_pow ((n : ℂ) + β) k).comp hNd
  have h2 := (tendsto_poch_neg_div_pow k).inv₀ one_ne_zero
  rw [inv_one] at h2
  simp only [inv_div] at h2
  have := (h1.mul h2).const_mul
    (poch (-(n : ℂ)) k * poch (-x) k / poch (β : ℂ) k / k.factorial * (-(d : ℂ)) ^ k)
  rw [mul_one, mul_one] at this
  have hz : (1 : ℂ) - ((c : ℂ))⁻¹ = -(d : ℂ) := by rw [hd]; push_cast; ring
  rw [hz, show poch (-(n : ℂ)) k * poch (-x) k / poch (β : ℂ) k * (-(d : ℂ)) ^ k /
      (k.factorial : ℂ) = poch (-(n : ℂ)) k * poch (-x) k / poch (β : ℂ) k /
      k.factorial * (-(d : ℂ)) ^ k by ring]
  refine this.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hd' : (d : ℂ) ≠ 0 := ofReal_ne_zero.mpr hd0.ne'
  simp only [Function.comp_apply, ofReal_mul, ofReal_natCast]
  have e1 : (n : ℂ) + (β - 1) + N * (((c⁻¹ : ℝ) : ℂ) - 1) + 1 = (n + β) + N * d := by
    rw [hd]; push_cast; ring
  have e : (-(d : ℂ)) ^ k * (-(N : ℂ)) ^ k = (N : ℂ) ^ k * d ^ k := by
    rw [← mul_pow, ← mul_pow]; ring_nf
  rw [e1, show (β : ℂ) - 1 + 1 = β by ring, one_pow, mul_pow]
  field_simp
  linear_combination (poch (-(n : ℂ)) k * poch (-x) k * poch ((n : ℂ) + β + d * N) k /
    (poch (β : ℂ) k * k.factorial * poch (-(N : ℂ)) k)) * e

@[dlmf 18.21.E8]
theorem meixner_limit_laguerrePolyL {α : ℝ} (hα : -1 < α) (n : ℕ) (x : ℂ) :
    Tendsto (fun c : ℝ => meixner (α + 1) c n (x / (1 - c : ℂ))) (𝓝[<] 1)
      (𝓝 (laguerrePolyL α n x / laguerrePolyL α n 0)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hp : poch ((α : ℂ) + 1) n / n.factorial ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat hα' n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have hL : laguerrePolyL α n x / laguerrePolyL α n 0 = kummerM (-n) (α + 1) x := by
    unfold laguerrePolyL
    rw [kummerM_zero, mul_one, mul_div_cancel_left₀ _ hp]
  have key : ∀ (c : ℝ), c ≠ 0 → c ≠ 1 → ∀ k : ℕ,
      poch (-(x / (1 - c : ℂ))) k * (1 - (c : ℂ)⁻¹) ^ k =
        ∏ i ∈ Finset.range k, ((x - i * (1 - c)) / c) := by
    intro c h0 h1 k
    have h0' : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr h0
    have h1' : (1 - c : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h1.symm)
    induction k with
    | zero => simp [poch_zero]
    | succ k ih =>
      rw [poch_succ, Finset.prod_range_succ, ← ih, pow_succ]
      field_simp
      ring
  rw [hL, kummerM_eq_sum_neg_nat]
  unfold meixner terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hprod : Tendsto (fun c : ℝ => ∏ i ∈ Finset.range k, ((x - i * (1 - c)) / c))
      (𝓝[<] 1) (𝓝 (x ^ k)) := by
    have h : Tendsto (fun c : ℝ => ∏ i ∈ Finset.range k, ((x - i * (1 - c)) / c)) (𝓝 1)
        (𝓝 (∏ i ∈ Finset.range k, ((x - i * (1 - ((1 : ℝ) : ℂ))) / ((1 : ℝ) : ℂ)))) := by
      apply tendsto_finsetProd
      intro i _
      exact (ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)).tendsto
    simp only [ofReal_one, sub_self, mul_zero, sub_zero, div_one, Finset.prod_const,
      Finset.card_range] at h
    exact h.mono_left nhdsWithin_le_nhds
  have := hprod.const_mul (poch (-(n : ℂ)) k / (poch ((α : ℂ) + 1) k * k.factorial))
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds zero_lt_one)]
    with c hc1 hc0
  rw [← key c hc0.ne' hc1.ne]
  ring

@[dlmf 18.21.E12]
theorem meixnerPollaczek_limit_laguerrePolyL {α : ℝ} (n : ℕ) (x : ℂ) :
    Tendsto (fun phi : ℝ => meixnerPollaczek ((α + 1) / 2) phi n (-x / (2 * (phi : ℂ))))
      (𝓝[>] 0) (𝓝 (laguerrePolyL α n x)) := by
  have hE0 : Tendsto (fun t : ℝ => 1 - cexp (-2 * I * t)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => 1 - cexp (-2 * I * t)) (𝓝 0)
        (𝓝 (1 - cexp (-2 * I * ((0 : ℝ) : ℂ)))) := Continuous.tendsto (by fun_prop) 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hE1 : Tendsto (fun t : ℝ => (1 - cexp (-2 * I * t)) / t) (𝓝[>] 0) (𝓝 (2 * I)) := by
    have hd := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (-2 * I)).cexp
    have h := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono (s := Set.Ioi (0 : ℝ)) _ fun t (ht : 0 < t) => ht.ne')
    have h' := h.neg
    simp only [id, ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h'
    rw [show -(-2 * I) = 2 * I by ring] at h'
    refine h'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [slope, sub_zero, vsub_eq_sub, Complex.real_smul, ofReal_inv, ofReal_zero,
      mul_zero, Complex.exp_zero]
    ring
  have hexp : Tendsto (fun t : ℝ => cexp (I * n * t)) (𝓝[>] 0) (𝓝 1) := by
    have h : Tendsto (fun t : ℝ => cexp (I * n * t)) (𝓝 0)
        (𝓝 (cexp (I * n * ((0 : ℝ) : ℂ)))) := Continuous.tendsto (by fun_prop) 0
    simpa using h.mono_left nhdsWithin_le_nhds
  unfold meixnerPollaczek laguerrePolyL terminatingHG
  rw [show 2 * (((α : ℂ) + 1) / 2) = α + 1 by ring, kummerM_eq_sum_neg_nat]
  have hpre : Tendsto (fun t : ℝ => poch ((α : ℂ) + 1) n / n ! * cexp (I * n * t)) (𝓝[>] 0)
      (𝓝 (poch ((α : ℂ) + 1) n / n !)) := by
    simpa using (tendsto_const_nhds (x := poch ((α : ℂ) + 1) n / n !)).mul hexp
  refine hpre.mul (tendsto_finsetSum _ fun k _ => ?_)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hfac : ∀ j : ℕ, Tendsto (fun t : ℝ => (((α : ℂ) + 1) / 2 + j) * (1 - cexp (-2 * I * t)) -
      I * x / 2 * ((1 - cexp (-2 * I * t)) / t)) (𝓝[>] 0) (𝓝 x) := by
    intro j
    have h := (hE0.const_mul (((α : ℂ) + 1) / 2 + j)).sub (hE1.const_mul (I * x / 2))
    convert h using 2
    ring_nf
    rw [I_sq]
    ring
  have hprod := (tendsto_finsetProd (Finset.range k) fun j _ => hfac j).const_mul
    (poch (-(n : ℂ)) k / (poch ((α : ℂ) + 1) k * k !))
  rw [Finset.prod_const, Finset.card_range] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
  rw [Finset.prod_congr rfl (g := fun j : ℕ => ((((α : ℂ) + 1) / 2 + I * (-x / (2 * t))) + j) *
    (1 - cexp (-2 * I * t))) (fun j _ => by field_simp; ring), ← poch_mul_pow]
  ring

@[dlmf 18.21.E13]
theorem meixnerPollaczek_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun lam : ℝ => n.factorial * (Real.sqrt lam : ℂ)⁻¹ ^ n *
      meixnerPollaczek lam (Real.pi / 2) n (x * Real.sqrt lam)) atTop (𝓝 (aeval x (hermitePolyH n))) := by
  have hsc : sin ((Real.pi : ℂ) / 2) = 1 := Complex.sin_pi_div_two
  have hcc : cos ((Real.pi : ℂ) / 2) = 0 := Complex.cos_pi_div_two
  refine tendsto_of_three_term (f := fun n lam => (n ! : ℂ) * (Real.sqrt lam : ℂ)⁻¹ ^ n *
      meixnerPollaczek lam (Real.pi / 2) n (x * Real.sqrt lam))
    (g := fun n => aeval x (hermitePolyH n))
    (A := fun n _ => 2 * x) (B := fun n lam => -((n + 1) * (2 + n / (lam : ℂ))))
    (A' := fun n => 2 * x) (B' := fun n => -((n + 1) * 2)) ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp [meixnerPollaczek, terminatingHG, poch_zero]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with lam hl
    have hs : (Real.sqrt lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hl).ne'
    have hl' : (lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr hl.ne'
    rw [meixnerPollaczek_one hl', hsc, hcc]
    simp only [hermitePolyH_one, map_mul, aeval_X, map_ofNat, Nat.factorial_one, Nat.cast_one]
    field_simp
    ring
  · intro n; exact tendsto_const_nhds
  · intro n
    simpa only [add_zero] using
      (((tendsto_const_div_ofReal_atTop (n : ℂ)).const_add 2).const_mul ((n : ℂ) + 1)).neg
  · intro n
    filter_upwards [eventually_gt_atTop 0] with lam hl
    have hs : (Real.sqrt lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hl).ne'
    have hs2 : (lam : ℂ) = (Real.sqrt lam : ℂ) ^ 2 := by
      rw [← ofReal_pow, Real.sq_sqrt hl.le]
    have hr := meixnerPollaczek_recurrence (lam := lam) (by simpa using hl)
      ((Real.pi : ℂ) / 2) n (x * Real.sqrt lam)
    rw [hsc, hcc, mul_comm x] at hr
    have hf2 : ((n + 2) ! : ℂ) = (n + 2) * (n + 1) * n ! := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    have hf1 : ((n + 1) ! : ℂ) = (n + 1) * n ! := by
      rw [Nat.factorial_succ]; push_cast; ring
    simp only [hf2, hf1, inv_pow]
    rw [hs2] at hr ⊢
    field_simp
    linear_combination ((n ! : ℂ) * (Real.sqrt lam : ℂ) ^ (2 * n + 3)) * hr
  · intro n
    rw [hermitePolyH_succ (n + 1), hermitePolyH_derivative]
    simp only [map_sub, map_mul, aeval_X, aeval_C, map_ofNat]
    push_cast
    ring

@[dlmf 18.22.E14]
theorem continuousHahn_difference_equation {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (n : ℕ) (x : ℂ) :
    (x + I * star a) * (x + I * star b) *
      (continuousHahn a b (star a) (star b) n (x + I) - continuousHahn a b (star a) (star b) n x) +
    (x - I * a) * (x - I * b) *
      (continuousHahn a b (star a) (star b) n (x - I) - continuousHahn a b (star a) (star b) n x) +
    n * (n + a + b + star a + star b - 1) * continuousHahn a b (star a) (star b) n x = 0 := by
  set c : ℂ := star a with hcdef
  set d : ℂ := star b with hddef
  have hAre : 0 < (a + c).re := by simp [hcdef]; linarith
  have hDre : 0 < (a + d).re := by simp [hddef]; linarith
  have hpA : ∀ k : ℕ, poch (a + c) k ≠ 0 := fun k => poch_ne_zero_of_re_pos hAre k
  have hpD : ∀ k : ℕ, poch (a + d) k ≠ 0 := fun k => poch_ne_zero_of_re_pos hDre k
  have hAk : ∀ k : ℕ, a + c + k ≠ 0 := fun k h => by
    have := congrArg re h; simp only [add_re, natCast_re, zero_re] at this hAre
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hDk : ∀ k : ℕ, a + d + k ≠ 0 := fun k h => by
    have := congrArg re h; simp only [add_re, natCast_re, zero_re] at this hDre
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  clear_value c d
  set s : ℂ := (n : ℂ) + a + b + c + d - 1 with hs
  set w : ℂ := a + I * x with hw
  set cf : ℕ → ℂ := fun k => poch (-(n : ℂ)) k * poch s k / (poch (a + c) k * poch (a + d) k) /
    k ! with hcf
  set G : ℕ → ℂ := fun k => cf k * ((n - k) * (n + k + a + b + c + d - 1) * poch w k) with hG
  set B : ℕ → ℂ := fun k => -((w - a - c) * (w - a - d)) * (poch (w - 1) k - poch w k) -
      w * (w - a + b) * (poch (w + 1) k - poch w k) +
      n * (n + a + b + c + d - 1) * poch w k with hB
  have hrec : ∀ k : ℕ, cf (k + 1) * ((k + 1) * (a + c + k) * (a + d + k)) =
      cf k * ((k - n) * (s + k)) := by
    intro k
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
    have := hpA k; have := hpD k; have := hAk k; have := hDk k
    simp only [hcf]
    rw [poch_succ, poch_succ s, poch_succ (a + c), poch_succ (a + d), Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have htel : ∀ k : ℕ, cf (k + 1) * B (k + 1) = G (k + 1) - G k := by
    intro k
    simp only [hB, hG]
    rw [ch_basis_succ a b c d w n k]
    have hr := hrec k
    push_cast
    linear_combination (poch w k) * hr
  have hkey : ∑ k ∈ Finset.range (n + 1), cf k * B k = 0 := by
    rw [Finset.sum_range_succ']
    simp_rw [htel]
    rw [Finset.sum_range_sub]
    simp only [hB, hG, hcf, poch_zero, sub_self]
    push_cast
    ring
  unfold continuousHahn terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  rw [show a + I * (x + I) = w - 1 by rw [hw]; linear_combination I_sq,
    show a + I * (x - I) = w + 1 by rw [hw]; linear_combination -I_sq,
    show (x + I * c) * (x + I * d) = -((w - a - c) * (w - a - d)) by
      rw [hw]; linear_combination (x ^ 2 + c * d) * I_sq,
    show (x - I * a) * (x - I * b) = -(w * (w - a + b)) by
      rw [hw]; linear_combination (x ^ 2 + a * b) * I_sq]
  have hfin : ∀ v : ℂ, ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
      (poch ((n : ℂ) + a + b + c + d - 1) k * poch v k) / (poch (a + c) k * poch (a + d) k) /
        (k ! : ℂ) = ∑ k ∈ Finset.range (n + 1), cf k * poch v k := fun v =>
    Finset.sum_congr rfl fun k _ => by simp only [hcf, hs]; ring
  rw [hfin, hfin, hfin, ← hw]
  clear_value B G cf w s
  have hexp : ∑ k ∈ Finset.range (n + 1), cf k * B k =
      -((w - a - c) * (w - a - d)) * (∑ k ∈ Finset.range (n + 1), cf k * poch (w - 1) k -
        ∑ k ∈ Finset.range (n + 1), cf k * poch w k) -
      w * (w - a + b) * (∑ k ∈ Finset.range (n + 1), cf k * poch (w + 1) k -
        ∑ k ∈ Finset.range (n + 1), cf k * poch w k) +
      n * (n + a + b + c + d - 1) * ∑ k ∈ Finset.range (n + 1), cf k * poch w k := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hB]
    ring
  rw [hkey] at hexp
  linear_combination (-(I ^ n * poch (a + c) n * poch (a + d) n / n !)) * hexp +
    (I ^ n * poch (a + c) n * poch (a + d) n / n ! * n *
      ∑ k ∈ Finset.range (n + 1), cf k * poch w k) * hs

@[dlmf 18.22.E17]
theorem meixnerPollaczek_difference_equation {lam : ℂ} (hlam : 0 < lam.re) (phi : ℂ) (n : ℕ) (x : ℂ) :
    exp (I * phi) * (x + I * lam) * (meixnerPollaczek lam phi n (x + I) - meixnerPollaczek lam phi n x) +
    exp (-I * phi) * (x - I * lam) * (meixnerPollaczek lam phi n (x - I) - meixnerPollaczek lam phi n x) +
    2 * n * sin phi * meixnerPollaczek lam phi n x = 0 := by
  have hp : ∀ k : ℕ, poch (2 * lam) k ≠ 0 := fun k => poch_ne_zero_of_re_pos (by simp; linarith) k
  have h2k : ∀ k : ℕ, 2 * lam + k ≠ 0 := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set z : ℂ := 1 - exp (-2 * I * phi) with hz
  set w : ℂ := lam + I * x with hw
  set c : ℕ → ℂ := fun k => poch (-(n : ℂ)) k / poch (2 * lam) k * z ^ k / k ! with hc
  set G : ℕ → ℂ := fun k => c k * (2 * (n - k) * sin phi * poch w k) with hG
  have hS := exp_mul_one_sub_exp phi
  -- the coefficient recurrence
  have hrec : ∀ k : ℕ, c (k + 1) * ((k + 1) * (k + 2 * lam)) = c k * ((k - n) * z) := by
    intro k
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
    have := hp k; have := h2k k
    simp only [hc]
    rw [poch_succ, poch_succ, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
    ring
  -- the basis action, telescoped
  set B : ℕ → ℂ := fun k => exp (I * phi) * (-I * (w - 2 * lam)) * (poch (w - 1) k - poch w k) +
      exp (-I * phi) * (-I * w) * (poch (w + 1) k - poch w k) + 2 * n * sin phi * poch w k with hB
  have htel : ∀ k : ℕ, c (k + 1) * B (k + 1) = G (k + 1) - G k := by
    intro k
    simp only [hB, hG]
    rw [mp_basis_succ lam phi w n k]
    have hr := hrec k
    have hz' : I * (exp (I * phi) * z) = -2 * sin phi := by
      rw [hz, hS]; linear_combination (2 * sin phi) * I_sq
    push_cast
    linear_combination (-(I * exp (I * phi) * poch w k)) * hr +
      (c k * (n - k) * poch w k) * hz'
  have hkey : ∑ k ∈ Finset.range (n + 1), c k * B k = 0 := by
    rw [Finset.sum_range_succ']
    simp_rw [htel]
    rw [Finset.sum_range_sub]
    simp only [hB, hG, hc, poch_zero, sub_self]
    push_cast
    ring
  unfold meixnerPollaczek terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [show lam + I * (x + I) = w - 1 by rw [hw]; linear_combination I_sq,
    show lam + I * (x - I) = w + 1 by rw [hw]; linear_combination -I_sq,
    show x + I * lam = -I * (w - 2 * lam) by rw [hw]; linear_combination x * I_sq,
    show x - I * lam = -I * w by rw [hw]; linear_combination x * I_sq]
  have hfin : ∀ v : ℂ, ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k * poch v k / poch (2 * lam) k *
      z ^ k / (k ! : ℂ) = ∑ k ∈ Finset.range (n + 1), c k * poch v k := fun v =>
    Finset.sum_congr rfl fun k _ => by simp only [hc]; ring
  rw [hfin, hfin, hfin, ← hw]
  clear_value B G c w z
  have hexp : ∑ k ∈ Finset.range (n + 1), c k * B k =
      exp (I * phi) * (-I * (w - 2 * lam)) * (∑ k ∈ Finset.range (n + 1), c k * poch (w - 1) k -
        ∑ k ∈ Finset.range (n + 1), c k * poch w k) +
      exp (-I * phi) * (-I * w) * (∑ k ∈ Finset.range (n + 1), c k * poch (w + 1) k -
        ∑ k ∈ Finset.range (n + 1), c k * poch w k) +
      2 * n * sin phi * ∑ k ∈ Finset.range (n + 1), c k * poch w k := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hB]
    ring
  rw [hkey] at hexp
  linear_combination (-(poch (2 * lam) n / n ! * exp (I * n * phi))) * hexp

@[dlmf 18.22.E27]
theorem continuousHahn_central_difference {a b c d : ℂ} (hac : 0 < (a + c).re) (had : 0 < (a + d).re) (n : ℕ) (x : ℂ) :
    (continuousHahn a b c d (n + 1) (x + I / 2) - continuousHahn a b c d (n + 1) (x - I / 2)) / I =
      (n + a + b + c + d) * continuousHahn (a + 1 / 2) (b + 1 / 2) (c + 1 / 2) (d + 1 / 2) n x := by
  have h0 : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h] at hz; simp at hz
  have hp : ∀ (z : ℂ) (k : ℕ), 0 < z.re → poch (z + 1) k ≠ 0 := fun z k hz =>
    poch_ne_zero_of_re_pos (by simp; linarith) k
  unfold continuousHahn terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [poch_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, sub_self, add_zero]
  rw [show a + I * (x + I / 2) = (a + I * x) - 1 / 2 by linear_combination (1 / 2 : ℂ) * I_sq,
    show a + I * (x - I / 2) = (a + I * x) + 1 / 2 by linear_combination (-1 / 2 : ℂ) * I_sq]
  rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have key := poch_half_sub (a + I * x) k
  rw [← sub_div, ← sub_div, ← mul_sub, ← mul_sub, key]
  rw [poch_succ_left (a + c), poch_succ_left (a + d),
    poch_succ_left (a + c) k, poch_succ_left (a + d) k,
    poch_succ_left (-((n + 1 : ℕ) : ℂ)), poch_succ_left (((n + 1 : ℕ) : ℂ) + a + b + c + d - 1),
    Nat.factorial_succ, Nat.factorial_succ,
    show a + 1 / 2 + (c + 1 / 2) = a + c + 1 by ring, show a + 1 / 2 + (d + 1 / 2) = a + d + 1 by ring,
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring,
    show ((n + 1 : ℕ) : ℂ) + a + b + c + d - 1 + 1 = (n : ℂ) + (a + 1 / 2) + (b + 1 / 2) +
      (c + 1 / 2) + (d + 1 / 2) - 1 by push_cast; ring,
    show a + I * x + 1 / 2 = a + 1 / 2 + I * x by ring, pow_succ]
  have := h0 _ hac; have := h0 _ had
  have := hp _ k hac; have := hp _ k had
  have := hp _ n hac; have := hp _ n had
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  push_cast
  field_simp
  ring

/-- Continuous Hahn coefficients are a convolution of two Kummer coefficient sequences. -/
theorem continuousHahn_coeff_convolution {a b c d : ℂ}
    (hac : 0 < (a + c).re) (had : 0 < (a + d).re) (hbd : 0 < (b + d).re)
    (x : ℂ) (n : ℕ) :
    continuousHahn a b c d n x / (poch (a + c) n * poch (b + d) n) =
      ∑ k ∈ Finset.range (n + 1),
        (kummerMCoeff (a + I * x) (a + c) k * (-I) ^ k) *
        (kummerMCoeff (d - I * x) (b + d) (n - k) * I ^ (n - k)) := by
  have hR := poch_ne_zero_of_re_pos hac
  have hD := poch_ne_zero_of_re_pos had
  have hT := poch_ne_zero_of_re_pos hbd
  have ht := terminating_3F2_convolution (a + I * x) (n + a + b + c + d - 1)
    (a + c) (a + d) hR n
  rw [show a + c - (n + a + b + c + d - 1) = 1 - (b + d) - n by ring,
    show a + d - (a + I * x) = d - I * x by ring] at ht
  have he : continuousHahn a b c d n x / (poch (a + c) n * poch (b + d) n) =
      I ^ n / (poch (b + d) n * n !) *
      ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * n.choose k * poch (a + I * x) k *
        poch (n + a + b + c + d - 1) k / poch (a + c) k * poch (a + d + k) (n - k) := by
    unfold continuousHahn terminatingHG
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
    rw [mul_div_assoc, Finset.mul_sum, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by simpa using hk
    rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
    have hp : poch (a + d) n = poch (a + d) k * poch (a + d + k) (n - k) := by
      rw [← poch_add, Nat.add_sub_cancel' hk']
    rw [hp]
    push_cast
    field_simp [hR n, hR k, hD k, hT n, Nat.cast_ne_zero.mpr k.factorial_ne_zero]
  rw [he, ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using hk
  have hp := poch_eq_poch_sub_mul (b + d) hk'
  have hf : (n.choose k : ℂ) * k ! * (n - k)! = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
  have hi : I ^ n = I ^ k * I ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hk']
  have hs : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hkf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hnk : ((n - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  have hpn : poch (1 - (b + d) - n) k = (-1) ^ k * poch (b + d) n / poch (b + d) (n-k) := by
    apply (eq_div_iff (hT (n-k))).2
    rw [hp]
    linear_combination -(poch (b+d) (n-k) * poch (1-(b+d)-n) k) * hs
  dsimp only [kummerMCoeff]
  rw [neg_pow, hi, hpn, ← hf]
  have hc : (n.choose k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hk').ne'
  field_simp [hR k, hT n, hT (n-k), hn, hkf, hnk, hc]


@[dlmf 18.23.E6]
theorem continuousHahn_generating_function {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (x z : ℂ) :
    HasSum (fun n : ℕ => continuousHahn a b (star a) (star b) n x /
      (poch (a + star a) n * poch (b + star b) n) * z ^ n)
      (kummerM (a + I * x) (a + star a) (-I * z) * kummerM (star b - I * x) (b + star b) (I * z)) := by
  have hac : 0 < (a + star a).re := by simp; linarith
  have had : 0 < (a + star b).re := by simp; linarith
  have hbd : 0 < (b + star b).re := by simp; linarith
  have hs1 := hasSum_kummerM (a := a + I * x) (not_neg_nat_of_re_pos hac) (-I * z)
  have hs2 := hasSum_kummerM (a := star b - I * x) (not_neg_nat_of_re_pos hbd) (I * z)
  have h1 : HasSum (fun n => (kummerMCoeff (a + I * x) (a + star a) n * (-I) ^ n) * z ^ n)
      (kummerM (a + I * x) (a + star a) (-I * z)) := by
    simpa only [mul_pow, mul_assoc] using hs1
  have h2 : HasSum (fun n => (kummerMCoeff (star b - I * x) (b + star b) n * I ^ n) * z ^ n)
      (kummerM (star b - I * x) (b + star b) (I * z)) := by
    simpa only [mul_pow, mul_assoc] using hs2
  have h := hasSum_coefficient_convolution h1 h2
  apply h.congr_fun
  intro n
  rw [continuousHahn_coeff_convolution hac had hbd]


/-! ### Orthogonality and recurrences of the discrete families

Orthogonality is obtained from the symmetry of the second-order difference operator
`B Δ⁺ + D Δ⁻` against the weight (summation by parts with the Pearson relation
`w(x+1) D(x+1) = w(x) B(x)`) and from distinct eigenvalues. The squared norms follow from
the three-term recurrences in the degree. -/

namespace DiscreteOrtho

/-- The second-order difference operator `B Δ⁺ + D Δ⁻` at a point. -/
def op (B D f : ℂ → ℂ) (x : ℂ) : ℂ :=
  B x * (f (x + 1) - f x) + D x * (f (x - 1) - f x)

/-- Summation by parts on `{0, …, N}`. -/
theorem sum_range_mul_op (N : ℕ) (w : ℕ → ℂ) (B D f g : ℂ → ℂ)
    (hD0 : D 0 = 0) (hBN : B N = 0)
    (hP : ∀ x < N, w (x + 1) * D ((x : ℂ) + 1) = w x * B x) :
    ∑ x ∈ Finset.range (N + 1), w x * g x * op B D f x =
      -∑ x ∈ Finset.range N, w x * B x * (f ((x : ℂ) + 1) - f x) *
        (g ((x : ℂ) + 1) - g x) := by
  simp only [op, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [hBN, Nat.cast_zero, hD0, mul_zero, zero_mul, add_zero]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  have h := hP x (Finset.mem_range.mp hx)
  push_cast
  rw [show (x : ℂ) + 1 - 1 = x by ring]
  linear_combination (g ((x : ℂ) + 1) * (f x - f ((x : ℂ) + 1))) * h

/-- Symmetry of the operator on `{0, …, N}`. -/
theorem sum_range_mul_op_symm (N : ℕ) (w : ℕ → ℂ) (B D f g : ℂ → ℂ)
    (hD0 : D 0 = 0) (hBN : B N = 0)
    (hP : ∀ x < N, w (x + 1) * D ((x : ℂ) + 1) = w x * B x) :
    ∑ x ∈ Finset.range (N + 1), w x * g x * op B D f x =
      ∑ x ∈ Finset.range (N + 1), w x * f x * op B D g x := by
  rw [sum_range_mul_op N w B D f g hD0 hBN hP, sum_range_mul_op N w B D g f hD0 hBN hP]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- Finite orthogonality from the eigenvalue equation. -/
theorem sum_range_orthogonal (N : ℕ) (w : ℕ → ℂ) (B D f g : ℂ → ℂ) {ef eg : ℂ}
    (hD0 : D 0 = 0) (hBN : B N = 0)
    (hP : ∀ x < N, w (x + 1) * D ((x : ℂ) + 1) = w x * B x)
    (hf : ∀ x : ℕ, x ≤ N → op B D f x = ef * f x)
    (hg : ∀ x : ℕ, x ≤ N → op B D g x = eg * g x) (hne : ef ≠ eg) :
    ∑ x ∈ Finset.range (N + 1), f x * g x * w x = 0 := by
  have h := sum_range_mul_op_symm N w B D f g hD0 hBN hP
  have e1 : ∑ x ∈ Finset.range (N + 1), w x * g x * op B D f x =
      ef * ∑ x ∈ Finset.range (N + 1), f x * g x * w x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hf x (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx))]
    ring
  have e2 : ∑ x ∈ Finset.range (N + 1), w x * f x * op B D g x =
      eg * ∑ x ∈ Finset.range (N + 1), f x * g x * w x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hg x (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx))]
    ring
  rw [e1, e2] at h
  have : (ef - eg) * ∑ x ∈ Finset.range (N + 1), f x * g x * w x = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)


/-- Summation by parts on `ℕ`. -/
theorem tsum_mul_op (w : ℕ → ℂ) (B D f g : ℂ → ℂ) (hD0 : D 0 = 0)
    (hP : ∀ x : ℕ, w (x + 1) * D ((x : ℂ) + 1) = w x * B x)
    (h1 : Summable fun x : ℕ => w x * g x * (B x * (f ((x : ℂ) + 1) - f x)))
    (h2 : Summable fun x : ℕ => w x * g x * (D x * (f ((x : ℂ) - 1) - f x))) :
    ∑' x : ℕ, w x * g x * op B D f x =
      -∑' x : ℕ, w x * B x * (f ((x : ℂ) + 1) - f x) * (g ((x : ℂ) + 1) - g x) := by
  have h2' := (summable_nat_add_iff 1).mpr h2
  have e : (fun x : ℕ => w x * g x * op B D f x) = fun x =>
      w x * g x * (B x * (f ((x : ℂ) + 1) - f x)) +
        w x * g x * (D x * (f ((x : ℂ) - 1) - f x)) := by
    funext x; simp only [op]; ring
  rw [e, h1.tsum_add h2, h2.tsum_eq_zero_add]
  simp only [Nat.cast_zero, hD0, zero_mul, mul_zero, zero_add]
  rw [← h1.tsum_add h2', ← tsum_neg]
  congr 1
  funext x
  have h := hP x
  push_cast
  rw [show (x : ℂ) + 1 - 1 = x by ring]
  linear_combination (g ((x : ℂ) + 1) * (f x - f ((x : ℂ) + 1))) * h

/-- Infinite orthogonality from the eigenvalue equation. -/
theorem tsum_orthogonal (w : ℕ → ℂ) (B D f g : ℂ → ℂ) {ef eg : ℂ} (hD0 : D 0 = 0)
    (hP : ∀ x : ℕ, w (x + 1) * D ((x : ℂ) + 1) = w x * B x)
    (h1 : Summable fun x : ℕ => w x * g x * (B x * (f ((x : ℂ) + 1) - f x)))
    (h2 : Summable fun x : ℕ => w x * g x * (D x * (f ((x : ℂ) - 1) - f x)))
    (h1' : Summable fun x : ℕ => w x * f x * (B x * (g ((x : ℂ) + 1) - g x)))
    (h2' : Summable fun x : ℕ => w x * f x * (D x * (g ((x : ℂ) - 1) - g x)))
    (hf : ∀ x : ℕ, op B D f x = ef * f x) (hg : ∀ x : ℕ, op B D g x = eg * g x)
    (hne : ef ≠ eg) :
    ∑' x : ℕ, f x * g x * w x = 0 := by
  have e1 : (fun x : ℕ => w x * g x * op B D f x) = fun x : ℕ => ef * (f x * g x * w x) := by
    funext x; rw [hf x]; ring
  have e2 : (fun x : ℕ => w x * f x * op B D g x) = fun x : ℕ => eg * (f x * g x * w x) := by
    funext x; rw [hg x]; ring
  have h3 : ∑' x : ℕ, w x * B x * (f ((x : ℂ) + 1) - f x) * (g ((x : ℂ) + 1) - g x) =
      ∑' x : ℕ, w x * B x * (g ((x : ℂ) + 1) - g x) * (f ((x : ℂ) + 1) - f x) := by
    congr 1; funext x; ring
  have h4 := (tsum_mul_op w B D f g hD0 hP h1 h2)
  have h5 := (tsum_mul_op w B D g f hD0 hP h1' h2')
  rw [e1, tsum_mul_left] at h4
  rw [e2, tsum_mul_left, ← h3, ← h4] at h5
  have : (ef - eg) * ∑' x : ℕ, f x * g x * w x = 0 := by linear_combination -h5
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

/-- Summability against a weight with polynomial moments. -/
theorem summable_mul_eval {w : ℕ → ℂ}
    (hw : ∀ K : ℕ, Summable fun x : ℕ => ‖w x‖ * ((x : ℝ) + 1) ^ K) (P : ℂ[X]) :
    Summable fun x : ℕ => w x * P.eval (x : ℂ) := by
  have e : (fun x : ℕ => w x * P.eval (x : ℂ)) = fun x =>
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (w x * (x : ℂ) ^ i) := by
    funext x
    rw [eval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e]
  refine summable_sum fun i _ => Summable.mul_left _ ?_
  refine Summable.of_norm_bounded (hw i) fun x => ?_
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg x) (by linarith) i)
    (norm_nonneg _)

/-- Ratio test for positive real sequences. -/
theorem summable_of_ratio_pos {u : ℕ → ℝ} (hu : ∀ n, 0 < u n) {l : ℝ} (hl : l < 1)
    (h : Tendsto (fun n => u (n + 1) / u n) atTop (𝓝 l)) : Summable u := by
  refine summable_of_ratio_test_tendsto_lt_one hl (Eventually.of_forall fun n => (hu n).ne') ?_
  simpa only [Real.norm_eq_abs, abs_of_pos (hu _)] using h

/-- `((n+2)/(n+1))^K → 1` as `n → ∞`. -/
theorem tendsto_succ_div_pow (K : ℕ) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1 + 1) / ((n : ℝ) + 1)) ^ K) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.const_add 1
  rw [add_zero] at h
  have : Tendsto (fun n : ℕ => ((n : ℝ) + 1 + 1) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    refine h.congr fun n => ?_
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  simpa using this.pow K

/-- Orthogonality on `ℕ` for polynomial eigenfunctions. -/
theorem hasSum_orthogonal_poly {w : ℕ → ℂ}
    (hw : ∀ K : ℕ, Summable fun x : ℕ => ‖w x‖ * ((x : ℝ) + 1) ^ K) (Bp Dp F G : ℂ[X])
    {ef eg : ℂ} (hD0 : Dp.eval 0 = 0)
    (hP : ∀ x : ℕ, w (x + 1) * Dp.eval ((x : ℂ) + 1) = w x * Bp.eval (x : ℂ))
    (hf : ∀ x : ℕ, op Bp.eval Dp.eval F.eval x = ef * F.eval (x : ℂ))
    (hg : ∀ x : ℕ, op Bp.eval Dp.eval G.eval x = eg * G.eval (x : ℂ)) (hne : ef ≠ eg) :
    HasSum (fun x : ℕ => F.eval (x : ℂ) * G.eval (x : ℂ) * w x) 0 := by
  have key : ∀ P Q R : ℂ[X], Summable fun x : ℕ =>
      w x * Q.eval (x : ℂ) * (R.eval (x : ℂ) * (P.eval ((x : ℂ) + 1) - P.eval (x : ℂ))) := by
    intro P Q R
    refine (summable_mul_eval hw (Q * (R * (P.comp (X + 1) - P)))).congr fun x => ?_
    simp only [eval_mul, eval_sub, eval_comp, eval_add, eval_X, eval_one]
    ring
  have key' : ∀ P Q R : ℂ[X], Summable fun x : ℕ =>
      w x * Q.eval (x : ℂ) * (R.eval (x : ℂ) * (P.eval ((x : ℂ) - 1) - P.eval (x : ℂ))) := by
    intro P Q R
    refine (summable_mul_eval hw (Q * (R * (P.comp (X - 1) - P)))).congr fun x => ?_
    simp only [eval_mul, eval_sub, eval_comp, eval_X, eval_one]
    ring
  have hs : Summable fun x : ℕ => F.eval (x : ℂ) * G.eval (x : ℂ) * w x :=
    (summable_mul_eval hw (F * G)).congr fun x => by simp only [eval_mul]; ring
  have h0 := tsum_orthogonal w Bp.eval Dp.eval F.eval G.eval hD0 hP (key F G Bp) (key' F G Dp)
    (key G F Bp) (key' G F Dp) hf hg hne
  rw [← h0]
  exact hs.hasSum

/-- For `a > 0` the Charlier weight `aˣ/x!` has finite moments of every order `K`. -/
theorem summable_charlierWeight {a : ℝ} (ha : 0 < a) (K : ℕ) :
    Summable fun x : ℕ => ‖(a : ℂ) ^ x / (x ! : ℂ)‖ * ((x : ℝ) + 1) ^ K := by
  have hu : ∀ n : ℕ, 0 < a ^ n / n ! * ((n : ℝ) + 1) ^ K := fun n => by positivity
  have h := summable_of_ratio_pos hu (l := 0) zero_lt_one ?_
  · refine h.congr fun x => ?_
    rw [norm_div, norm_pow, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
      abs_of_pos ha]
  have e : ∀ n : ℕ, a ^ (n + 1) / (n + 1)! * (((n + 1 : ℕ) : ℝ) + 1) ^ K /
      (a ^ n / n ! * ((n : ℝ) + 1) ^ K) =
      a * (1 / ((n : ℝ) + 1)) * (((n : ℝ) + 1 + 1) / ((n : ℝ) + 1)) ^ K := by
    intro n
    have h1 : (n ! : ℝ) ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [Nat.factorial_succ, div_pow]
    push_cast
    field_simp
    ring
  simp_rw [e]
  have := ((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul a).mul (tendsto_succ_div_pow K))
  simpa using this

/-- `C_0(x; a) = 1`. -/
theorem charlier_zero (a x : ℂ) : charlier a 0 x = 1 := by
  simp [charlier, terminatingHG, poch_zero]

/-- `C_1(x; a) = 1 - x/a`. -/
theorem charlier_one {a : ℂ} (ha : a ≠ 0) (x : ℂ) : charlier a 1 x = 1 - x / a := by
  simp [charlier, terminatingHG, Finset.sum_range_succ, poch_zero, poch_one]
  field_simp
  ring

/-- The Charlier recurrence in the form `x C_n = …`. -/
theorem charlier_mul_x {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    x * charlier a n x = (n + a) * charlier a n x - a * charlier a (n + 1) x -
      n * charlier a (n - 1) x := by
  cases n with
  | zero =>
    rw [charlier_zero, charlier_one ha]
    field_simp
    ring
  | succ k =>
    have h := charlier_recurrence ha k x
    simp only [Nat.add_sub_cancel]
    push_cast
    linear_combination h

/-- A two-numerator terminating sum `₂F_q(-n, -x; b; z)` as a polynomial in `x`. -/
def hgPoly (n : ℕ) (b : List ℂ) (z : ℂ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (poch (-(n : ℂ)) k / (b.map (fun t => poch t k)).prod *
    z ^ k / k.factorial) * (ascPochhammer ℂ k).comp (-X)

/-- Evaluating `hgPoly n b z` at `x` gives the terminating sum `F(-n, -x; b; z)`. -/
theorem eval_hgPoly (n : ℕ) (b : List ℂ) (z x : ℂ) :
    (hgPoly n b z).eval x = terminatingHG n [-(n : ℂ), -x] b z := by
  simp only [hgPoly, terminatingHG, eval_finsetSum, eval_mul, eval_C, eval_comp, eval_neg, eval_X,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [poch]; ring

/-- The Meixner polynomial is the evaluation of `hgPoly n [β] (1 - 1/c)`. -/
theorem eval_hgPoly_meixner (β c : ℂ) (n : ℕ) (x : ℂ) :
    (hgPoly n [β] (1 - c⁻¹)).eval x = meixner β c n x := eval_hgPoly _ _ _ _

/-- For `β > 0` and `0 < c < 1` the Meixner weight `(β)_x cˣ/x!` has finite moments of
every order. -/
theorem summable_meixnerWeight {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (hc1 : c < 1) (K : ℕ) :
    Summable fun x : ℕ => ‖poch (β : ℂ) x * (c : ℂ) ^ x / (x ! : ℂ)‖ * ((x : ℝ) + 1) ^ K := by
  have hp : ∀ n : ℕ, poch (β : ℂ) n ≠ 0 := poch_ne_zero_of_re_pos (by simpa using hβ)
  have hu : ∀ n : ℕ, 0 < ‖poch (β : ℂ) n‖ * c ^ n / n ! * ((n : ℝ) + 1) ^ K := fun n => by
    have := norm_pos_iff.mpr (hp n); positivity
  have h := summable_of_ratio_pos hu (l := c) hc1 ?_
  · refine h.congr fun x => ?_
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Complex.norm_natCast, Real.norm_eq_abs,
      abs_of_pos hc]
  have hb : ∀ n : ℕ, ‖(β : ℂ) + n‖ = β + n := fun n => by
    rw [show (β : ℂ) + n = ((β + n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have e : ∀ n : ℕ, ‖poch (β : ℂ) (n + 1)‖ * c ^ (n + 1) / (n + 1)! *
      (((n + 1 : ℕ) : ℝ) + 1) ^ K / (‖poch (β : ℂ) n‖ * c ^ n / n ! * ((n : ℝ) + 1) ^ K) =
      (1 + (β - 1) * (1 / ((n : ℝ) + 1))) * c *
        (((n : ℝ) + 1 + 1) / ((n : ℝ) + 1)) ^ K := by
    intro n
    have h1 : (n ! : ℝ) ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h3 : ‖poch (β : ℂ) n‖ ≠ 0 := norm_ne_zero_iff.mpr (hp n)
    rw [poch_succ, norm_mul, hb, Nat.factorial_succ, div_pow]
    push_cast
    field_simp
    ring
  simp_rw [e]
  have := (((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (β - 1)).const_add 1).mul_const
    c).mul (tendsto_succ_div_pow K)
  simpa using this

/-- `M_0(x; β, c) = 1`. -/
theorem meixner_zero (β c x : ℂ) : meixner β c 0 x = 1 := by
  simp [meixner, terminatingHG, poch_zero]

end DiscreteOrtho

open DiscreteOrtho in
/-- The Meixner recurrence in the degree (DLMF 18.22.2 with Table 18.22.1). -/
@[dlmf 18.22.E2]
theorem meixner_recurrence {β c : ℂ} (hβ : 0 < β.re) (hc : c ≠ 0) (n : ℕ) (x : ℂ) :
    (c - 1) * x * meixner β c (n + 1) x =
      c * (n + 1 + β) * meixner β c (n + 2) x -
        (n + 1 + (n + 1 + β) * c) * meixner β c (n + 1) x + (n + 1) * meixner β c n x := by
  have hint : ∀ m : ℕ, (c - 1) * m * meixner β c (n + 1) m =
      c * (n + 1 + β) * meixner β c (n + 2) m -
        (n + 1 + (n + 1 + β) * c) * meixner β c (n + 1) m + (n + 1) * meixner β c n m := by
    intro m
    have h := meixner_difference_equation hβ hc m ((n + 1 : ℕ) : ℂ)
    rw [show ((n + 1 : ℕ) : ℂ) + 1 = ((n + 2 : ℕ) : ℂ) by push_cast; ring,
      show ((n + 1 : ℕ) : ℂ) - 1 = ((n : ℕ) : ℂ) by push_cast; ring,
      meixner_duality β c m (n + 2), meixner_duality β c m (n + 1),
      meixner_duality β c m n] at h
    push_cast at h
    linear_combination -h
  have hpoly : C (c - 1) * X * hgPoly (n + 1) [β] (1 - c⁻¹) =
      C (c * (n + 1 + β)) * hgPoly (n + 2) [β] (1 - c⁻¹) -
        C (n + 1 + (n + 1 + β) * c) * hgPoly (n + 1) [β] (1 - c⁻¹) +
          C ((n : ℂ) + 1) * hgPoly n [β] (1 - c⁻¹) := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (m : ℂ))
      Nat.cast_injective fun m => ?_
    simp only [Set.mem_ofPred_eq, eval_mul, eval_sub, eval_add, eval_C, eval_X,
      eval_hgPoly_meixner]
    rw [hint m]
  have := congrArg (eval x) hpoly
  simp only [eval_mul, eval_sub, eval_add, eval_C, eval_X, eval_hgPoly_meixner] at this
  rw [this]

namespace DiscreteOrtho

/-- The Meixner recurrence written as `(c - 1) x M_n = …` for all `n`. -/
theorem meixner_mul_x {β c : ℂ} (hβ : 0 < β.re) (hc : c ≠ 0) (n : ℕ) (x : ℂ) :
    (c - 1) * x * meixner β c n x = c * (n + β) * meixner β c (n + 1) x -
      (n + (n + β) * c) * meixner β c n x + n * meixner β c (n - 1) x := by
  cases n with
  | zero =>
    have hβ0 : β ≠ 0 := fun h => by simp [h] at hβ
    simp only [meixner_zero, Nat.cast_zero, zero_add, zero_mul, add_zero, mul_one]
    simp [meixner, terminatingHG, Finset.sum_range_succ, poch_zero, poch_one]
    field_simp
    ring
  | succ k =>
    have h := meixner_recurrence hβ hc k x
    simp only [Nat.add_sub_cancel]
    push_cast
    linear_combination h

end DiscreteOrtho

open DiscreteOrtho in
@[dlmf 18.19.T1]
theorem charlier_orthogonality {a : ℝ} (ha : 0 < a) (m n : ℕ) :
    HasSum (fun x : ℕ => charlier a m x * charlier a n x * (a : ℂ) ^ x / x.factorial)
      (if m = n then (a : ℂ)⁻¹ ^ n * exp a * n.factorial else 0) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set w : ℕ → ℂ := fun x => (a : ℂ) ^ x / (x ! : ℂ) with hwdef
  have hw := summable_charlierWeight ha
  have hP : ∀ x : ℕ, w (x + 1) * (X : ℂ[X]).eval ((x : ℂ) + 1) =
      w x * (C (a : ℂ)).eval (x : ℂ) := by
    intro x
    simp only [hwdef, eval_X, eval_C, Nat.factorial_succ]
    push_cast
    have : (x ! : ℂ) ≠ 0 := by exact_mod_cast x.factorial_ne_zero
    field_simp
    ring
  have hE : ∀ (k : ℕ) (x : ℕ), op (C (a : ℂ)).eval (X : ℂ[X]).eval (charlierPoly a k).eval x =
      (-(k : ℂ)) * (charlierPoly a k).eval (x : ℂ) := by
    intro k x
    simp only [op, eval_C, eval_X, eval_charlierPoly]
    linear_combination charlier_difference_equation ha' k x
  have hO : ∀ k l : ℕ, k ≠ l →
      HasSum (fun x : ℕ => charlier a k x * charlier a l x * w x) 0 := by
    intro k l hkl
    have h := hasSum_orthogonal_poly hw (C (a : ℂ)) X (charlierPoly a k) (charlierPoly a l)
      (by simp) hP (hE k) (hE l) (by
        intro h; apply hkl; exact_mod_cast neg_inj.mp h)
    simpa only [eval_charlierPoly] using h
  have hS : ∀ P : ℂ[X], Summable fun x : ℕ => w x * P.eval (x : ℂ) := summable_mul_eval hw
  have hsq : ∀ k : ℕ, Summable fun x : ℕ => charlier a k x * charlier a k x * w x := by
    intro k
    refine (hS (charlierPoly a k * charlierPoly a k)).congr fun x => ?_
    simp only [eval_mul, eval_charlierPoly]; ring
  -- the squared norms
  have hN : ∀ k : ℕ, HasSum (fun x : ℕ => charlier a k x * charlier a k x * w x)
      ((a : ℂ)⁻¹ ^ k * exp a * k.factorial) := by
    intro k
    induction k with
    | zero =>
      simp only [charlier_zero, one_mul, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
      have he : HasSum (fun x : ℕ => (a : ℂ) ^ x / x !) (exp a) := by
        simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (a : ℂ)
      exact he
    | succ k ih =>
      -- T(x) = x C_{k+1} C_k w
      have hT1 : HasSum (fun x : ℕ => (x : ℂ) * charlier a (k + 1) x * charlier a k x * w x)
          (-((k : ℂ) + 1) * ((a : ℂ)⁻¹ ^ k * exp a * k.factorial)) := by
        have h := (((hO (k + 1) k (by omega)).mul_left ((k + 1 : ℕ) + (a : ℂ))).sub
          ((hO (k + 2) k (by omega)).mul_left (a : ℂ))).sub (ih.mul_left ((k + 1 : ℕ) : ℂ))
        convert h using 1
        · funext x
          have := charlier_mul_x ha' (k + 1) x
          simp only [Nat.add_sub_cancel] at this
          push_cast at this ⊢
          linear_combination charlier a k x * w x * this
        · push_cast; ring
      have hT2 : HasSum (fun x : ℕ => (x : ℂ) * charlier a (k + 1) x * charlier a k x * w x)
          (-(a : ℂ) * ∑' x : ℕ, charlier a (k + 1) x * charlier a (k + 1) x * w x) := by
        have h := ((((hO (k + 1) k (by omega)).mul_left ((k : ℂ) + a)).sub
          ((hsq (k + 1)).hasSum.mul_left (a : ℂ))).sub
          ((hO (k + 1) (k - 1) (by omega)).mul_left (k : ℂ)))
        convert h using 1
        · funext x
          have := charlier_mul_x ha' k x
          linear_combination charlier a (k + 1) x * w x * this
        · ring
      have hv := hT1.unique hT2
      set S := ∑' x : ℕ, charlier a (k + 1) x * charlier a (k + 1) x * w x
      have : S = (a : ℂ)⁻¹ ^ (k + 1) * exp a * (k + 1).factorial := by
        rw [Nat.factorial_succ, pow_succ]
        push_cast
        have e : S = -(a : ℂ)⁻¹ * (-(a : ℂ) * S) := by field_simp
        rw [e, ← hv]
        ring
      rw [← this]
      exact (hsq (k + 1)).hasSum
  split_ifs with hmn
  · subst hmn
    simpa only [hwdef, mul_div_assoc] using hN m
  · simpa only [hwdef, mul_div_assoc] using hO m n hmn

open DiscreteOrtho in
@[dlmf 18.19.T1]
theorem meixner_orthogonality {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (hc1 : c < 1) (m n : ℕ) :
    HasSum (fun x : ℕ => meixner β c m x * meixner β c n x * poch β x *
      (c : ℂ) ^ x / x.factorial)
      (if m = n then (c : ℂ)⁻¹ ^ n * n.factorial / (poch β n * (1 - c : ℂ) ^ (β : ℂ)) else 0) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hc1' : (c : ℂ) - 1 ≠ 0 := by
    intro h; have : (c : ℂ) = 1 := by linear_combination h
    exact hc1.ne (by exact_mod_cast this)
  have hβre : 0 < (β : ℂ).re := by simpa using hβ
  have hp : ∀ n : ℕ, poch (β : ℂ) n ≠ 0 := poch_ne_zero_of_re_pos hβre
  set w : ℕ → ℂ := fun x => poch (β : ℂ) x * (c : ℂ) ^ x / (x ! : ℂ) with hwdef
  have hw := summable_meixnerWeight hβ hc hc1
  have hP : ∀ x : ℕ, w (x + 1) * (X : ℂ[X]).eval ((x : ℂ) + 1) =
      w x * (C (c : ℂ) * (X + C (β : ℂ))).eval (x : ℂ) := by
    intro x
    simp only [hwdef, eval_X, eval_C, eval_mul, eval_add, Nat.factorial_succ, poch_succ]
    push_cast
    have : (x ! : ℂ) ≠ 0 := by exact_mod_cast x.factorial_ne_zero
    field_simp
    ring
  set P : ℕ → ℂ[X] := fun k => hgPoly k [(β : ℂ)] (1 - (c : ℂ)⁻¹) with hPdef
  have hE : ∀ (k : ℕ) (x : ℕ), op (C (c : ℂ) * (X + C (β : ℂ))).eval (X : ℂ[X]).eval
      (P k).eval x = (-(k : ℂ) * (1 - c)) * (P k).eval (x : ℂ) := by
    intro k x
    simp only [hPdef, op, eval_C, eval_X, eval_mul, eval_add, eval_hgPoly_meixner]
    linear_combination meixner_difference_equation hβre hc' k x
  have hO : ∀ k l : ℕ, k ≠ l →
      HasSum (fun x : ℕ => meixner β c k x * meixner β c l x * w x) 0 := by
    intro k l hkl
    have h := hasSum_orthogonal_poly hw (C (c : ℂ) * (X + C (β : ℂ))) X (P k) (P l)
      (by simp) hP (hE k) (hE l) (by
        intro h
        have : ((k : ℂ) - l) * (1 - c) = 0 := by linear_combination -h
        rcases mul_eq_zero.mp this with h' | h'
        · exact hkl (by exact_mod_cast sub_eq_zero.mp h')
        · exact hc1' (by linear_combination -h'))
    simpa only [hPdef, eval_hgPoly_meixner] using h
  have hsq : ∀ k : ℕ, Summable fun x : ℕ => meixner β c k x * meixner β c k x * w x := by
    intro k
    refine (summable_mul_eval hw (P k * P k)).congr fun x => ?_
    simp only [hPdef, eval_mul, eval_hgPoly_meixner]; ring
  have hN : ∀ k : ℕ, HasSum (fun x : ℕ => meixner β c k x * meixner β c k x * w x)
      ((c : ℂ)⁻¹ ^ k * k.factorial / (poch β k * (1 - c : ℂ) ^ (β : ℂ))) := by
    intro k
    induction k with
    | zero =>
      simp only [meixner_zero, one_mul, pow_zero, Nat.factorial_zero, Nat.cast_one, poch_zero]
      have hcn : ‖(c : ℂ)‖ < 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]; exact hc1
      have h := hasSum_poch_div_factorial (β := (β : ℂ)) hcn
      rw [cpow_neg] at h
      convert h using 1
      · funext x; simp only [hwdef]; ring
      · ring
    | succ k ih =>
      set S := ∑' x : ℕ, meixner β c (k + 1) x * meixner β c (k + 1) x * w x
      have hT1 : HasSum (fun x : ℕ =>
          ((c : ℂ) - 1) * x * meixner β c (k + 1) x * meixner β c k x * w x)
          ((k + 1 : ℂ) * ((c : ℂ)⁻¹ ^ k * k.factorial / (poch β k * (1 - c : ℂ) ^ (β : ℂ)))) := by
        have h := (((hO (k + 2) k (by omega)).mul_left ((c : ℂ) * ((k + 1 : ℕ) + β))).sub
          ((hO (k + 1) k (by omega)).mul_left (((k + 1 : ℕ) : ℂ) + ((k + 1 : ℕ) + β) * c))).add
          (ih.mul_left ((k + 1 : ℕ) : ℂ))
        convert h using 1
        · funext x
          have := meixner_mul_x hβre hc' (k + 1) x
          simp only [Nat.add_sub_cancel] at this
          push_cast at this ⊢
          linear_combination meixner β c k x * w x * this
        · push_cast; ring
      have hT2 : HasSum (fun x : ℕ =>
          ((c : ℂ) - 1) * x * meixner β c (k + 1) x * meixner β c k x * w x)
          ((c : ℂ) * (k + β) * S) := by
        have h := ((((hsq (k + 1)).hasSum.mul_left ((c : ℂ) * (k + β))).sub
          ((hO (k + 1) k (by omega)).mul_left ((k : ℂ) + (k + β) * c))).add
          ((hO (k + 1) (k - 1) (by omega)).mul_left (k : ℂ)))
        convert h using 1
        · funext x
          have := meixner_mul_x hβre hc' k x
          linear_combination meixner β c (k + 1) x * w x * this
        · ring
      have hv := hT1.unique hT2
      have hkb : (k : ℂ) + β ≠ 0 := by
        intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      have : S = (c : ℂ)⁻¹ ^ (k + 1) * (k + 1).factorial /
          (poch β (k + 1) * (1 - c : ℂ) ^ (β : ℂ)) := by
        have e : S = ((c : ℂ) * (k + β))⁻¹ * ((c : ℂ) * (k + β) * S) := by field_simp
        rw [e, ← hv, poch_succ, Nat.factorial_succ, pow_succ]
        push_cast
        have h1 : (1 - c : ℂ) ^ (β : ℂ) ≠ 0 := by
          rw [Ne, cpow_eq_zero_iff]; push Not; intro h
          exact absurd (by linear_combination -h : (c : ℂ) = 1) (fun h' => hc1' (by rw [h']; ring))
        have h2 := hp k
        have h3 : (β : ℂ) + k ≠ 0 := by rw [add_comm]; exact hkb
        field_simp
        ring
      rw [← this]
      exact (hsq (k + 1)).hasSum
  split_ifs with hmn
  · subst hmn
    simpa only [hwdef, mul_div_assoc, mul_assoc] using hN m
  · simpa only [hwdef, mul_div_assoc, mul_assoc] using hO m n hmn

/-- `K_0(x; p, N) = 1`. -/
theorem krawtchouk_zero (p : ℂ) (N : ℕ) (x : ℂ) : krawtchouk p N 0 x = 1 := by
  simp [krawtchouk, terminatingHG, poch_zero]

/-- The Krawtchouk recurrence in the degree at the lattice points (DLMF 18.22.2). -/
theorem krawtchouk_mul_x_nat {p : ℂ} (hp : p ≠ 0) {N n m : ℕ} (hn : n ≤ N) (hm : m ≤ N) :
    (m : ℂ) * krawtchouk p N n m =
      p * (n - N) * (krawtchouk p N (n + 1) m - krawtchouk p N n m) +
        (p - 1) * n * (krawtchouk p N (n - 1) m - krawtchouk p N n m) := by
  have h := krawtchouk_difference_equation hp hm (n : ℂ)
  have e0 : krawtchouk p N m n = krawtchouk p N n m := krawtchouk_duality p hm hn
  have e1 : p * (n - N) * krawtchouk p N m ((n : ℂ) + 1) =
      p * (n - N) * krawtchouk p N (n + 1) m := by
    rcases Nat.lt_or_ge n N with h' | h'
    · rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring,
        krawtchouk_duality p hm (by omega)]
    · have : (n : ℂ) = N := by exact_mod_cast le_antisymm hn h'
      rw [this]; ring
  have e2 : (p - 1) * n * krawtchouk p N m ((n : ℂ) - 1) =
      (p - 1) * n * krawtchouk p N (n - 1) m := by
    cases n with
    | zero => simp
    | succ k =>
      rw [show ((k + 1 : ℕ) : ℂ) - 1 = (k : ℂ) by push_cast; ring,
        krawtchouk_duality p hm (by omega), Nat.add_sub_cancel]
  rw [e0] at h
  linear_combination -h + e1 + e2

@[dlmf 18.19.T1]
theorem krawtchouk_orthogonality {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {N m n : ℕ} (hm : m ≤ N) (hn : n ≤ N) :
    ∑ x ∈ Finset.range (N + 1), krawtchouk p N m x * krawtchouk p N n x *
      N.choose x * (p : ℂ) ^ x * (1 - p : ℂ) ^ (N - x) =
      if m = n then (((1 - p) / p : ℂ) ^ n / N.choose n) else 0 := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (1 - p : ℂ) ≠ 0 := by
    intro h; have : (p : ℂ) = 1 := by linear_combination -h
    exact hp1.ne (by exact_mod_cast this)
  set w : ℕ → ℂ := fun x => N.choose x * (p : ℂ) ^ x * (1 - p : ℂ) ^ (N - x) with hwdef
  set B : ℂ → ℂ := fun x => p * (N - x)
  set D : ℂ → ℂ := fun x => (1 - p) * x
  have hP : ∀ x < N, w (x + 1) * D ((x : ℂ) + 1) = w x * B x := by
    intro x hx
    simp only [hwdef, B, D]
    have hc : ((N.choose (x + 1) : ℕ) : ℂ) * ((x : ℂ) + 1) = N.choose x * ((N : ℂ) - x) := by
      have := congrArg (Nat.cast (R := ℂ)) (Nat.choose_succ_right_eq N x)
      push_cast [Nat.cast_sub hx.le] at this
      exact this
    have hpow : (1 - p : ℂ) ^ (N - x) = (1 - p : ℂ) ^ (N - (x + 1)) * (1 - p) := by
      rw [← pow_succ]; congr 1; omega
    rw [hpow, pow_succ]
    linear_combination (p : ℂ) ^ x * (p : ℂ) * (1 - p : ℂ) ^ (N - (x + 1)) * (1 - p) * hc
  have hE : ∀ k ≤ N, ∀ x : ℕ, x ≤ N →
      DiscreteOrtho.op B D (krawtchouk p N k) x = (-(k : ℂ)) * krawtchouk p N k x := by
    intro k hk x _
    simp only [DiscreteOrtho.op, B, D]
    linear_combination -krawtchouk_difference_equation hp' hk (x : ℂ)
  have hO : ∀ k l : ℕ, k ≤ N → l ≤ N → k ≠ l →
      ∑ x ∈ Finset.range (N + 1), krawtchouk p N k x * krawtchouk p N l x * w x = 0 := by
    intro k l hk hl hkl
    exact DiscreteOrtho.sum_range_orthogonal N w B D _ _ (by simp [D]) (by simp [B]) hP
      (hE k hk) (hE l hl) (fun h => hkl (by exact_mod_cast neg_inj.mp h))
  have hRec : ∀ k ≤ N, ∀ x ∈ Finset.range (N + 1), (x : ℂ) * krawtchouk p N k x =
      p * (k - N) * (krawtchouk p N (k + 1) x - krawtchouk p N k x) +
        (p - 1) * k * (krawtchouk p N (k - 1) x - krawtchouk p N k x) := fun k hk x hx =>
    krawtchouk_mul_x_nat hp' hk (Nat.lt_succ_iff.mp (Finset.mem_range.mp hx))
  set h : ℕ → ℂ := fun k =>
    ∑ x ∈ Finset.range (N + 1), krawtchouk p N k x * krawtchouk p N k x * w x with hh
  have hN : ∀ k ≤ N, h k = ((1 - p) / p : ℂ) ^ k / N.choose k := by
    intro k hk
    induction k with
    | zero =>
      simp only [hh, hwdef, krawtchouk_zero, one_mul, pow_zero, Nat.choose_zero_right,
        Nat.cast_one, div_one]
      have := (add_pow (p : ℂ) (1 - p) N).symm
      rw [show (p : ℂ) + (1 - p) = 1 by ring, one_pow] at this
      refine (Finset.sum_congr rfl fun x _ => ?_).trans this
      ring
    | succ k ih =>
      have ih := ih (by omega)
      set T := ∑ x ∈ Finset.range (N + 1),
        (x : ℂ) * krawtchouk p N (k + 1) x * krawtchouk p N k x * w x
      have hT1 : T = (p - 1) * (k + 1) * h k := by
        have e : T = ∑ x ∈ Finset.range (N + 1),
            (p * ((k + 1 : ℕ) - N) * (krawtchouk p N (k + 2) x * krawtchouk p N k x * w x -
              krawtchouk p N (k + 1) x * krawtchouk p N k x * w x) +
            (p - 1) * (k + 1 : ℕ) * (krawtchouk p N k x * krawtchouk p N k x * w x -
              krawtchouk p N (k + 1) x * krawtchouk p N k x * w x)) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have := hRec (k + 1) hk x hx
          simp only [Nat.add_sub_cancel] at this
          linear_combination krawtchouk p N k x * w x * this
        rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib, hO (k + 1) k hk (by omega) (by omega)]
        have h2 : p * (((k + 1 : ℕ) : ℂ) - N) * ∑ x ∈ Finset.range (N + 1),
            krawtchouk p N (k + 2) x * krawtchouk p N k x * w x = 0 := by
          rcases Nat.lt_or_ge (k + 1) N with h' | h'
          · rw [hO (k + 2) k (by omega) (by omega) (by omega), mul_zero]
          · have : ((k + 1 : ℕ) : ℂ) = N := by exact_mod_cast le_antisymm hk h'
            rw [this]; ring
        simp only [sub_zero]
        rw [h2, zero_add]
        simp only [hh]
        push_cast; ring
      have hT2 : T = p * (k - N) * h (k + 1) := by
        have e : T = ∑ x ∈ Finset.range (N + 1),
            (p * (k - N) * (krawtchouk p N (k + 1) x * krawtchouk p N (k + 1) x * w x -
              krawtchouk p N (k + 1) x * krawtchouk p N k x * w x) +
            (p - 1) * k * (krawtchouk p N (k + 1) x * krawtchouk p N (k - 1) x * w x -
              krawtchouk p N (k + 1) x * krawtchouk p N k x * w x)) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have := hRec k (by omega) x hx
          linear_combination krawtchouk p N (k + 1) x * w x * this
        rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib, hO (k + 1) k hk (by omega) (by omega),
          hO (k + 1) (k - 1) hk (by omega) (by omega)]
        simp only [hh]
        ring
      have hkN : (k : ℂ) - N ≠ 0 := by
        intro h0; have : (k : ℂ) = N := by linear_combination h0
        have : k = N := by exact_mod_cast this
        omega
      have hch : (N.choose (k + 1) : ℂ) * ((k : ℂ) + 1) = N.choose k * ((N : ℂ) - k) := by
        have := congrArg (Nat.cast (R := ℂ)) (Nat.choose_succ_right_eq N k)
        push_cast [Nat.cast_sub (by omega : k ≤ N)] at this
        exact this
      have hc0 : (N.choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
      have hc1 : (N.choose (k + 1) : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
      have hv := hT1.symm.trans hT2
      rw [ih] at hv
      have e : h (k + 1) = ((p : ℂ) * ((k : ℂ) - N))⁻¹ * ((p : ℂ) * ((k : ℂ) - N) * h (k + 1)) := by
        field_simp
      have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have hch' : (N.choose (k + 1) : ℂ) = N.choose k * ((N : ℂ) - k) / ((k : ℂ) + 1) := by
        rw [eq_div_iff hk1, hch]
      have hNk : (N : ℂ) - k ≠ 0 := by intro h0; exact hkN (by linear_combination -h0)
      rw [e, ← hv, pow_succ, hch']
      field_simp
      ring
  split_ifs with hmn
  · subst hmn
    rw [← hN m hm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hwdef]; ring
  · rw [← hO m n hm hn hmn]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hwdef]; ring


@[dlmf 18.19.T1]
theorem hahn_orthogonal {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {N m n : ℕ}
    (hm : m ≤ N) (hn : n ≤ N) (hmn : m ≠ n) :
    ∑ x ∈ Finset.range (N + 1), hahn α β N m x * hahn α β N n x *
      poch (α + 1) x * poch (β + 1) (N - x) / ((x.factorial : ℂ) * (N - x).factorial) = 0 := by
  have hαre : -1 < (α : ℂ).re := by simpa using hα
  set w : ℕ → ℂ := fun x => poch ((α : ℂ) + 1) x * poch ((β : ℂ) + 1) (N - x) /
    ((x.factorial : ℂ) * (N - x).factorial) with hwdef
  set B : ℂ → ℂ := fun x => (x + α + 1) * (N - x)
  set D : ℂ → ℂ := fun x => x * (N + β + 1 - x)
  have hP : ∀ x < N, w (x + 1) * D ((x : ℂ) + 1) = w x * B x := by
    intro x hx
    simp only [hwdef, B, D]
    obtain ⟨j, rfl⟩ : ∃ j, N = x + 1 + j := ⟨N - (x + 1), by omega⟩
    rw [show x + 1 + j - (x + 1) = j by omega, show x + 1 + j - x = j + 1 by omega,
      poch_succ, poch_succ, Nat.factorial_succ, Nat.factorial_succ]
    have h1 : (x.factorial : ℂ) ≠ 0 := by exact_mod_cast x.factorial_ne_zero
    have h2 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    push_cast
    field_simp
    ring
  have hE : ∀ k ≤ N, ∀ x : ℕ, x ≤ N →
      DiscreteOrtho.op B D (hahn α β N k) x =
        (-((k : ℂ) * (k + α + β + 1))) * hahn α β N k x := by
    intro k hk x _
    simp only [DiscreteOrtho.op, B, D]
    linear_combination -hahn_difference_equation (β := (β : ℂ)) hαre hk (x : ℂ)
  have hne : -((m : ℂ) * (m + α + β + 1)) ≠ -((n : ℂ) * (n + α + β + 1)) := by
    intro h
    have e : ((m : ℂ) - n) * (m + n + α + β + 1) = 0 := by linear_combination -h
    have e' : (((m : ℝ) - n) * (m + n + α + β + 1) : ℝ) = 0 := by exact_mod_cast e
    rcases mul_eq_zero.mp e' with h' | h'
    · exact hmn (by exact_mod_cast sub_eq_zero.mp h')
    · have : (1 : ℝ) ≤ m + n := by
        have : 1 ≤ m + n := by omega
        exact_mod_cast this
      linarith
  have h := DiscreteOrtho.sum_range_orthogonal N w B D _ _ (by simp [D])
    (by simp [B]) hP (hE m hm) (hE n hn) hne
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [hwdef]
  ring

/-- `hgPoly n b z` has degree at most `n`. -/
theorem natDegree_hgPoly_le (n : ℕ) (b : List ℂ) (z : ℂ) :
    (DiscreteOrtho.hgPoly n b z).natDegree ≤ n := by
  unfold DiscreteOrtho.hgPoly
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_comp, ascPochhammer_natDegree, natDegree_neg, natDegree_X, mul_one]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)

/-- The Krawtchouk polynomial is the evaluation of `hgPoly n [-N] (1/p)`. -/
theorem eval_hgPoly_krawtchouk (p : ℂ) (N n : ℕ) (x : ℂ) :
    (DiscreteOrtho.hgPoly n [-(N : ℂ)] p⁻¹).eval x = krawtchouk p N n x :=
  DiscreteOrtho.eval_hgPoly _ _ _ _

/-- The Krawtchouk recurrence in the degree (DLMF 18.22.2 with Table 18.22.1). -/
@[dlmf 18.22.E2]
theorem krawtchouk_recurrence {p : ℂ} (hp : p ≠ 0) {N n : ℕ} (hn : n + 1 ≤ N) (x : ℂ) :
    -x * krawtchouk p N n x = p * (N - n) * krawtchouk p N (n + 1) x -
      (p * (N - n) + n * (1 - p)) * krawtchouk p N n x +
        n * (1 - p) * krawtchouk p N (n - 1) x := by
  set K : ℕ → ℂ[X] := fun k => DiscreteOrtho.hgPoly k [-(N : ℂ)] p⁻¹ with hK
  have hpoly : -X * K n = C (p * (N - n)) * K (n + 1) - C (p * (N - n) + n * (1 - p)) * K n +
      C (n * (1 - p)) * K (n - 1) := by
    refine eq_of_natDegree_lt_card_of_eval_eq _ _ (f := fun i : Fin (N + 1) => ((i : ℕ) : ℂ))
      (fun i j h => Fin.ext (Nat.cast_injective h)) (fun i => ?_) ?_
    · have hi : (i : ℕ) ≤ N := Nat.lt_succ_iff.mp i.isLt
      simp only [hK, eval_mul, eval_sub, eval_add, eval_neg, eval_C, eval_X,
        eval_hgPoly_krawtchouk]
      have := krawtchouk_mul_x_nat hp (by omega : n ≤ N) hi
      linear_combination -this
    · have h1 : (-X * K n).natDegree ≤ N := by
        refine (natDegree_mul_le).trans ?_
        have : (K n).natDegree ≤ n := natDegree_hgPoly_le n [-(N : ℂ)] p⁻¹
        simp only [natDegree_neg, natDegree_X]
        omega
      have h2 : (C (p * (N - n)) * K (n + 1) - C (p * (N - n) + n * (1 - p)) * K n +
          C (n * (1 - p)) * K (n - 1)).natDegree ≤ N := by
        refine (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans
          (max_le ?_ ?_)) ?_) <;> refine (natDegree_C_mul_le _ _).trans ?_
        · exact (natDegree_hgPoly_le _ _ _).trans hn
        · exact (natDegree_hgPoly_le _ _ _).trans (by omega)
        · exact (natDegree_hgPoly_le _ _ _).trans (by omega)
      simp only [Fintype.card_fin]
      omega
  have := congrArg (eval x) hpoly
  simp only [hK, eval_mul, eval_sub, eval_add, eval_neg, eval_C, eval_X,
    eval_hgPoly_krawtchouk] at this
  exact this

/-- The total mass of the Hahn weight, the case `n = 0` of Table 18.19.1. -/
@[dlmf 18.19.T1]
theorem hahn_weight_sum (α β : ℂ) (N : ℕ) :
    ∑ x ∈ Finset.range (N + 1), poch (α + 1) x * poch (β + 1) (N - x) /
      ((x.factorial : ℂ) * (N - x).factorial) = poch (α + β + 2) N / N.factorial := by
  have h := poch_add_eq_sum (α + 1) (β + 1) N
  rw [show α + 1 + (β + 1) = α + β + 2 by ring] at h
  rw [h, Finset.sum_div]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
  have hc : (N.choose x : ℂ) = N.factorial / ((x.factorial : ℂ) * (N - x).factorial) := by
    rw [Nat.choose_eq_factorial_div_factorial hx',
      Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hx')
        (by exact_mod_cast (Nat.mul_pos (Nat.factorial_pos x) (Nat.factorial_pos _)).ne')]
    push_cast; ring
  have h1 : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
  have h2 : (x.factorial : ℂ) ≠ 0 := by exact_mod_cast x.factorial_ne_zero
  have h3 : ((N - x).factorial : ℂ) ≠ 0 := by exact_mod_cast (N - x).factorial_ne_zero
  rw [hc]
  field_simp

namespace HahnRec

/-- The dual basis `(-m)_k (m + s)_k` in the degree variable. -/
def phi (s m : ℂ) (k : ℕ) : ℂ := poch (-m) k * poch (m + s) k

/-- The recurrence operator on the dual basis, with denominators cleared. -/
theorem op_phi_succ (α β N n : ℂ) (j : ℕ) :
    (2 * n + (α + β + 1) - 1) * (n + (α + β + 1)) * (n + α + 1) * (N - n) *
        phi (α + β + 1) (n + 1) (j + 1) -
      ((2 * n + (α + β + 1) - 1) * (n + (α + β + 1)) * (n + α + 1) * (N - n) +
        (2 * n + (α + β + 1) + 1) * n * (n + (α + β + 1) + N) * (n + β)) *
        phi (α + β + 1) n (j + 1) +
      (2 * n + (α + β + 1) + 1) * n * (n + (α + β + 1) + N) * (n + β) *
        phi (α + β + 1) (n - 1) (j + 1) =
      (2 * n + (α + β + 1) - 1) * (2 * n + (α + β + 1)) * (2 * n + (α + β + 1) + 1) *
        (-((j : ℂ) + 1) * phi (α + β + 1) n (j + 1) +
          (α + j + 1) * (j - N) * (j + 1) * phi (α + β + 1) n j) := by
  set s := α + β + 1 with hs
  set U := poch (-n) j
  set Up := poch (-n + 1) j
  set V := poch (n + s) j
  set Vp := poch (n + s + 1) j
  have hU : U * (-n + j) = (-n) * Up := by
    rw [← poch_succ, poch_succ_left]
  have hV : V * (n + s + j) = (n + s) * Vp := by
    rw [← poch_succ, poch_succ_left]
  have e1 : phi s (n + 1) (j + 1) = (-n - 1) * U * (Vp * (n + s + 1 + j)) := by
    simp only [phi, U, Vp]
    rw [poch_succ_left, show -(n + 1) + 1 = -n by ring, show -(n + 1) = -n - 1 by ring,
      show n + 1 + s = n + s + 1 by ring, poch_succ]
  have e2 : phi s n (j + 1) = U * (-n + j) * (V * (n + s + j)) := by
    simp only [phi, U, V]
    rw [poch_succ, poch_succ]
  have e3 : phi s (n - 1) (j + 1) = Up * (-n + 1 + j) * ((n + s - 1) * V) := by
    simp only [phi, Up, V]
    rw [show -(n - 1) = -n + 1 by ring, poch_succ, show n - 1 + s = n + s - 1 by ring,
      poch_succ_left, show n + s - 1 + 1 = n + s by ring]
  have e4 : phi s n j = U * V := rfl
  rw [e1, e2, e3, e4]
  linear_combination
    ((2 * n + s + 1) * (n + s + N) * (n + β) * (-n + 1 + j) * (n + s - 1) * V) * hU +
    (-(2 * n + s - 1) * (n + α + 1) * (N - n) * (-n - 1) * U * (n + s + 1 + j)) * hV

/-- The coefficient `1 / ((α+1)_k (-N)_k k!)`. -/
def dcoef (α : ℂ) (N : ℕ) (k : ℕ) : ℂ := (poch (α + 1) k * poch (-(N : ℂ)) k * k.factorial)⁻¹

/-- The Hahn polynomial as a sum over `k ≤ K` (any `K ≥ m`) of
`dcoef α N k (-x)_k (-m)_k (m+α+β+1)_k`. -/
theorem hahn_eq_sum (α β : ℂ) (N m K : ℕ) (hm : m ≤ K) (x : ℂ) :
    hahn α β N m x = ∑ k ∈ Finset.range (K + 1),
      dcoef α N k * poch (-x) k * phi (α + β + 1) m k := by
  unfold hahn terminatingHG
  have hsub : Finset.range (m + 1) ⊆ Finset.range (K + 1) :=
    Finset.range_mono (Nat.add_le_add_right hm 1)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [dcoef, phi, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      one_pow]
    rw [show (m : ℂ) + α + β + 1 = m + (α + β + 1) by ring]
    field_simp
  · intro k _ hk
    have : m < k := by simp at hk; omega
    simp [phi, poch_neg_nat_eq_zero this]

/-- The ratio of consecutive coefficients `dcoef α N j`. -/
theorem dcoef_succ {α : ℂ} (hα : -1 < α.re) {N j : ℕ} (hj : j + 1 ≤ N) :
    dcoef α N (j + 1) * ((α + j + 1) * (j - N) * (j + 1)) = dcoef α N j := by
  have h1 : poch (α + 1) j ≠ 0 := poch_ne_zero_of_re_pos (by simp; linarith) j
  have h2 : poch (-(N : ℂ)) j ≠ 0 := by
    rw [poch_neg_coe_nat]
    refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega)).ne'
  have h3 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have h4 : α + j + 1 ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have h5 : (j : ℂ) - N ≠ 0 := by
    intro h; have : (j : ℂ) = N := by linear_combination h
    have : j = N := by exact_mod_cast this
    omega
  have h6 : (j : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  simp only [dcoef]
  rw [poch_succ, poch_succ, Nat.factorial_succ]
  push_cast
  have e : α + 1 + j = α + j + 1 := by ring
  rw [e]
  field_simp
  have : ((j : ℂ) - N)⁻¹ * ((j : ℂ) - N) = 1 := inv_mul_cancel₀ h5
  linear_combination this

end HahnRec

open HahnRec in
/-- The three-term recurrence of the Hahn polynomials in the degree, DLMF 18.22.2 with
Table 18.22.1, multiplied through by `(2n+α+β)(2n+α+β+1)(2n+α+β+2)`. -/
@[dlmf 18.22.E2]
theorem hahn_recurrence {α β : ℂ} (hα : -1 < α.re) {N n : ℕ} (hn : n + 1 ≤ N) (x : ℂ) :
    (2 * n + α + β) * (2 * n + α + β + 1) * (2 * n + α + β + 2) * (-x * hahn α β N n x) =
      (2 * n + α + β) * (n + α + β + 1) * (n + α + 1) * (N - n) * hahn α β N (n + 1) x -
        ((2 * n + α + β) * (n + α + β + 1) * (n + α + 1) * (N - n) +
          (2 * n + α + β + 2) * n * (n + α + β + N + 1) * (n + β)) * hahn α β N n x +
        (2 * n + α + β + 2) * n * (n + α + β + N + 1) * (n + β) * hahn α β N (n - 1) x := by
  set s := α + β + 1 with hs
  set A' := (2 * (n : ℂ) + s - 1) * (n + s) * (n + α + 1) * (N - n)
  set C' := (2 * (n : ℂ) + s + 1) * n * (n + s + N) * (n + β)
  set D' := (2 * (n : ℂ) + s - 1) * (2 * n + s) * (2 * n + s + 1)
  set c : ℕ → ℂ := fun k => dcoef α N k * poch (-x) k
  have hQ1 := hahn_eq_sum α β N (n + 1) (n + 1) le_rfl x
  have hQ0 := hahn_eq_sum α β N n (n + 1) (Nat.le_succ n) x
  have hQm : C' * hahn α β N (n - 1) x =
      C' * ∑ k ∈ Finset.range (n + 1 + 1), c k * phi s ((n : ℂ) - 1) k := by
    cases n with
    | zero => simp [C']
    | succ k =>
      rw [hahn_eq_sum α β N (k + 1 - 1) (k + 1 + 1) (by omega) x]
      congr 2
      funext i
      simp only [c]
      rw [show ((k + 1 - 1 : ℕ) : ℂ) = ((k + 1 : ℕ) : ℂ) - 1 by push_cast; ring]
  -- the operator acting termwise
  have hterm : ∀ k ∈ Finset.range (n + 1 + 1),
      c k * (A' * phi s ((n : ℂ) + 1) k - (A' + C') * phi s n k + C' * phi s ((n : ℂ) - 1) k) =
        D' * (-(k : ℂ) * (c k * phi s n k)) +
          (if k = 0 then 0 else D' * (dcoef α N (k - 1) * poch (-x) k * phi s n (k - 1))) := by
    intro k hk
    rcases k with _ | j
    · simp [phi, poch_zero]
    · have hj : j + 1 ≤ N := by simp at hk; omega
      have hb := op_phi_succ α β N n j
      have hd := dcoef_succ hα hj
      simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, c]
      rw [← hd]
      push_cast
      simp only [A', C', D']
      rw [show (α + β + 1) = s from rfl] at hb
      linear_combination (dcoef α N (j + 1) * poch (-x) (j + 1)) * hb
  -- assemble
  have hsum : A' * hahn α β N (n + 1) x - (A' + C') * hahn α β N n x +
      C' * hahn α β N (n - 1) x = ∑ k ∈ Finset.range (n + 1 + 1),
        c k * (A' * phi s ((n : ℂ) + 1) k - (A' + C') * phi s n k +
          C' * phi s ((n : ℂ) - 1) k) := by
    rw [hQm, hQ1, hQ0, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [c]
    push_cast
    ring
  have h2 : ∑ k ∈ Finset.range (n + 1 + 1), (if k = 0 then 0 else
      D' * (dcoef α N (k - 1) * poch (-x) k * phi s n (k - 1))) =
      ∑ j ∈ Finset.range (n + 1), D' * (dcoef α N j * poch (-x) (j + 1) * phi s n j) := by
    rw [Finset.sum_range_succ']
    simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, h2] at hsum
  -- telescoping identity
  have htel : ∑ k ∈ Finset.range (n + 1 + 1), D' * (-(k : ℂ) * (c k * phi s n k)) +
      ∑ j ∈ Finset.range (n + 1), D' * (dcoef α N j * poch (-x) (j + 1) * phi s n j) =
      D' * (-x * hahn α β N n x) := by
    have hz : phi s n (n + 1) = 0 := by
      simp [phi, poch_neg_nat_eq_zero (Nat.lt_succ_self n)]
    rw [Finset.sum_range_succ, hz, mul_zero, mul_zero, mul_zero, add_zero,
      ← Finset.sum_add_distrib, hahn_eq_sum α β N n n le_rfl x, ← hs, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [c]
    rw [poch_succ]
    ring
  have hD'eq : D' = (2 * n + α + β) * (2 * n + α + β + 1) * (2 * n + α + β + 2) := by
    simp only [D', hs]; ring
  rw [← hD'eq, ← htel, ← hsum]
  simp only [A', C', hs]
  ring


/-- The inner Chu–Vandermonde sum for the explicit Meixner formula. -/
theorem meixner_explicit_inner {n j : ℕ} (hj : j ≤ n) (x β : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * n.choose k * k.choose j * poch (-x) k *
      poch (β + k) (n - k) = (-1 : ℂ) ^ j * n.choose j * poch (-x) j * poch (x + β) (n - j) := by
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : j ≤ n + 1)]
  have h0 : ∑ k ∈ Finset.range j, (-1 : ℂ) ^ k * n.choose k * k.choose j * poch (-x) k *
      poch (β + k) (n - k) = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hk)]; simp
  rw [h0, zero_add, Finset.sum_Ico_eq_sum_range, show n + 1 - j = n - j + 1 by omega]
  have hv := chu_vandermonde_sum (n - j) (-x + j) (β + j)
  rw [show β + j - (-x + j) = x + β by ring] at hv
  rw [← hv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n - j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hc := Nat.choose_mul (n := n) (k := j + i) (s := j) (by omega)
  rw [show j + i - j = i by omega] at hc
  have hc' : (n.choose (j + i) : ℂ) * ((j + i).choose j) = n.choose j * (n - j).choose i := by
    exact_mod_cast hc
  rw [poch_add, show n - (j + i) = n - j - i by omega, pow_add]
  push_cast
  rw [show β + (j + i : ℂ) = β + j + i by ring]
  linear_combination ((-1 : ℂ) ^ j * (-1 : ℂ) ^ i * poch (-x) j * poch (-x + j) i *
    poch (β + j + i) (n - j - i)) * hc'

/-- The explicit Meixner sum needs only the denominator factors up to its degree to be
nonzero. This includes the negative-integer specialization defining Krawtchouk polynomials. -/
theorem poch_mul_meixner_eq_sum_of_ne_zero {β c : ℂ} (n : ℕ)
    (hβ : ∀ k ≤ n, poch β k ≠ 0) (x : ℂ) :
    poch β n * meixner β c n x =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * poch (-x) k * poch (x + β) (n - k) *
        c⁻¹ ^ k := by
  -- rewrite the Meixner sum
  have e1 : poch β n * meixner β c n x = ∑ k ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ k * n.choose k * poch (-x) k * poch (β + k) (n - k) * (-c⁻¹ + 1) ^ k := by
    unfold meixner terminatingHG
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hp : poch β n = poch β k * poch (β + k) (n - k) := by
      rw [← poch_add, Nat.add_sub_cancel' hk']
    have hd : poch (-(n : ℂ)) k = (-1 : ℂ) ^ k * n.choose k * k.factorial := by
      rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
      push_cast; ring
    have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hp, hd, show (1 : ℂ) - c⁻¹ = -c⁻¹ + 1 by ring]
    field_simp [hβ k hk']
  -- expand the binomial and swap
  have e2 : ∀ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * n.choose k * poch (-x) k *
      poch (β + k) (n - k) * (-c⁻¹ + 1) ^ k = ∑ j ∈ Finset.range (n + 1),
        (-c⁻¹) ^ j * ((-1 : ℂ) ^ k * n.choose k * k.choose j * poch (-x) k *
          poch (β + k) (n - k)) := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [add_pow, Finset.mul_sum]
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : k + 1 ≤ n + 1)]
    have h0 : ∑ j ∈ Finset.Ico (k + 1) (n + 1), (-c⁻¹) ^ j * ((-1 : ℂ) ^ k * n.choose k *
        k.choose j * poch (-x) k * poch (β + k) (n - k)) = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [Nat.choose_eq_zero_of_lt (n := k) (k := j) (by simp at hj; omega)]; simp
    rw [h0, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [one_pow, mul_one]
    ring
  rw [e1, Finset.sum_congr rfl e2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← Finset.mul_sum, meixner_explicit_inner hj' x β, neg_pow]
  have h1 : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (n.choose j * poch (-x) j * poch (x + β) (n - j) * c⁻¹ ^ j) * h1

/-- An explicit sum for the Meixner polynomials (Beals–Wong (6.5.2)):
`(β)_n M_n(x; β, c) = ∑_k C(n,k) (-x)_k (x + β)_{n-k} c^{-k}`. -/
theorem poch_mul_meixner_eq_sum {β c : ℂ} (hβ : 0 < β.re) (n : ℕ) (x : ℂ) :
    poch β n * meixner β c n x =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * poch (-x) k * poch (x + β) (n - k) *
        c⁻¹ ^ k :=
  poch_mul_meixner_eq_sum_of_ne_zero n (fun k _ => poch_ne_zero_of_re_pos hβ k) x

end DLMF.OrthogonalPolynomials
