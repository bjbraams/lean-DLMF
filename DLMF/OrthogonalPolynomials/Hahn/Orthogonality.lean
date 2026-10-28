/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Hahn.CharlierAndConnections

/-!
# Orthogonality and recurrences of discrete polynomial families

Moment summation and generating functions establish orthogonality and recurrence relations of
discrete polynomial families.

Source references and common attribution are retained in
`DLMF.OrthogonalPolynomials.Hahn`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter

open scoped Real Nat Topology

open DLMF.Hypergeometric

open DLMF.Confluent

noncomputable section

set_option autoImplicit false

namespace DLMF.OrthogonalPolynomials

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
/-- The series with terms `(fun x : ℕ => charlier a m x * charlier a n x * (a : ℂ) ^ x /
x.factorial)` converges to `(if m = n then (a : ℂ)⁻¹ ^ n * exp a * n.factorial else 0)`. -/
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
/-- The series with terms `(fun x : ℕ => meixner β c m x * meixner β c n x * poch β x * (c : ℂ) ^
x / x.factorial)` converges to `(if m = n then (c : ℂ)⁻¹ ^ n * n.factorial / (poch β n * (1 -
c : ℂ) ^ (β : ℂ)) else 0)`. -/
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

/-- Formula under the stated hypotheses: `∑ x ∈ Finset.range (N + 1), krawtchouk p N m x *
krawtchouk p N n x * N.choose x * (p : ℂ) ^ x * (1 - p : ℂ) ^ (N - x) = if m = n then (((1 -
p) / p : ℂ) ^ n / N.choose n) else 0`. -/
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

/-- Formula under the stated hypotheses: `∑ x ∈ Finset.range (N + 1), hahn α β N m x * hahn α β N
n x * poch (α + 1) x * poch (β + 1) (N - x) / ((x.factorial : ℂ) * (N - x).factorial) = 0`. -/
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

end
end
