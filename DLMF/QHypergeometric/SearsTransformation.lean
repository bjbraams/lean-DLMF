/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bailey
public import DLMF.QHypergeometric.Convergence

/-!
# Sears' transformation of a terminating balanced `₄φ₃` and its limits (DLMF 17.9)

The terminating very-well-poised `₈φ₇` of Watson's transformation (`DLMF.Bailey`) is symmetric
in its four free parameters, while the balanced `₄φ₃` it equals singles out a pair of them.
Comparing two pairings gives Sears' transformations of a terminating balanced `₄φ₃`. Letting
parameters tend to `0` or `∞` gives the terminating `₃φ₂` and `₂φ₁` transformations of
DLMF 17.9.2, 17.9.5 and 17.9.8–17.9.11.

## Main definitions

* `searsSum`: the terminating `₄φ₃(q⁻ⁿ,…;q,q)` as a finite sum.
* `phiSum`: the terminating `₃φ₂(q⁻ⁿ,…;q,z)` as a finite sum.

## Main results

* `searsSum_transformation_first`, `searsSum_transformation_second`: Sears' transformations
  (DLMF 17.9.14), cleared of denominators.
* `searsSum_three_two_first`, `phiSum_three_two_second`, `phiSum_three_two_third`,
  `searsSum_three_two_fourth`: the terminating `₃φ₂` transformations (DLMF 17.9.8–17.9.11).
* `phiSum_two_one_three_one`, `phiSum_two_one_sears`: the terminating `₂φ₁` transformations
  (DLMF 17.9.2, 17.9.5).
* `qPhi_four_three_eq_searsSum`, `qPhi_three_two_eq_searsSum`, `qPhi_three_two_eq_phiSum`,
  `qPhi_two_one_eq_phiSum`, `qPhi_three_one_eq_sum`: the terminating `qPhi` as finite sums.

## Implementation notes

Watson's transformation is available in rational form when `(Aq;q)_{2n} ≠ 0`. The two pairings
are compared on a punctured neighbourhood of the very-well-poised parameter `A`, and the
transformation at `A` itself follows by continuity in `A`; only the denominators of the two
balanced sums need to be nonzero. The limits are taken in the same way: the transformation
holds on a punctured neighbourhood of the limit point and both sides are continuous there,
after parameters tending to `∞` are written as `1/t`. Degenerate parameters (`b = 0`, `d = 0`,
`e = 0`) that the limiting statements allow are reached by a second continuity argument.
-/

@[expose] public noncomputable section

open Complex Filter Finset
open scoped Topology
open DLMF.QSeries DLMF.Bailey

namespace DLMF.QHypergeometric

/-- The terminating `₄φ₃(q⁻ⁿ,x₁,x₂,x₃;y₁,y₂,y₃;q,q)` as a finite sum. -/
def searsSum (q : ℂ) (n : ℕ) (x₁ x₂ x₃ y₁ y₂ y₃ : ℂ) : ℂ :=
  ∑ k ∈ range (n + 1), qPochhammer (q⁻¹ ^ n) q k * qPochhammer x₁ q k * qPochhammer x₂ q k *
    qPochhammer x₃ q k / (qPochhammer y₁ q k * qPochhammer y₂ q k * qPochhammer y₃ q k *
      qPochhammer q q k) * q ^ k

/-- The terminating `₃φ₂(q⁻ⁿ,x₁,x₂;y₁,y₂;q,z)` as a finite sum. -/
def phiSum (q : ℂ) (n : ℕ) (x₁ x₂ y₁ y₂ z : ℂ) : ℂ :=
  ∑ k ∈ range (n + 1), qPochhammer (q⁻¹ ^ n) q k * qPochhammer x₁ q k * qPochhammer x₂ q k /
    (qPochhammer y₁ q k * qPochhammer y₂ q k * qPochhammer q q k) * z ^ k

namespace SearsTransformation

/-- Points avoiding a single value form an eventual set in the punctured neighbourhood. -/
private lemma eventually_ne (a c : ℂ) : ∀ᶠ t in 𝓝[≠] a, t ≠ c := by
  by_cases h : a = c
  · subst h; exact self_mem_nhdsWithin
  · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds h)

/-- `(tκ;q)_n ≠ 0` for `t` near, but different from, any point. -/
lemma eventually_qPochhammer_mul_ne_zero {κ q : ℂ} (hκ : κ ≠ 0) (hq : q ≠ 0) (a : ℂ) (n : ℕ) :
    ∀ᶠ t in 𝓝[≠] a, qPochhammer (t * κ) q n ≠ 0 := by
  have h : ∀ᶠ t in 𝓝[≠] a, ∀ i ∈ range n, t ≠ (κ * q ^ i)⁻¹ :=
    (eventually_all_finset _).mpr fun i _ => eventually_ne a _
  filter_upwards [h] with t ht
  rw [qPochhammer_eq_prod, prod_ne_zero_iff]
  intro i hi h0
  have hqi : κ * q ^ i ≠ 0 := mul_ne_zero hκ (pow_ne_zero _ hq)
  exact ht i hi (eq_inv_of_mul_eq_one_left (by linear_combination -h0))

/-- `(tκ;q)_n ≠ 0` for `t` near, but different from, any point, for any `κ`. -/
lemma eventually_qPochhammer_mul_ne_zero' (κ : ℂ) {q : ℂ} (hq : q ≠ 0) (a : ℂ) (n : ℕ) :
    ∀ᶠ t in 𝓝[≠] a, qPochhammer (t * κ) q n ≠ 0 := by
  by_cases hκ : κ = 0
  · subst hκ; exact Eventually.of_forall fun t => by simp [qPochhammer_zero_param]
  · exact eventually_qPochhammer_mul_ne_zero hκ hq a n

/-- `(κ/t;q)_n ≠ 0` for `t` near, but different from, any point. -/
lemma eventually_qPochhammer_div_ne_zero (κ q a : ℂ) (n : ℕ) :
    ∀ᶠ t in 𝓝[≠] a, qPochhammer (κ / t) q n ≠ 0 := by
  have h : ∀ᶠ t in 𝓝[≠] a, ∀ i ∈ range n, t ≠ κ * q ^ i :=
    (eventually_all_finset _).mpr fun i _ => eventually_ne a _
  filter_upwards [h, eventually_ne a 0] with t ht ht0
  rw [qPochhammer_eq_prod, prod_ne_zero_iff]
  intro i hi h0
  exact ht i hi (by field_simp at h0; linear_combination h0)

/-- Two functions continuous at `a` that agree on a punctured neighbourhood agree at `a`. -/
lemma eq_of_eventually_punctured {f g : ℂ → ℂ} {a : ℂ} (hf : ContinuousAt f a)
    (hg : ContinuousAt g a) (h : ∀ᶠ t in 𝓝[≠] a, f t = g t) : f a = g a := by
  have h1 : Tendsto f (𝓝[≠] a) (𝓝 (f a)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[≠] a) (𝓝 (g a)) :=
    (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun t ht => ht.symm)
  exact tendsto_nhds_unique h1 h2

/-- `watsonR4` in terms of `searsSum`. -/
lemma sum_watsonR4 (A b c d e q : ℂ) (n : ℕ) :
    ∑ k ∈ range (n + 1), watsonR4 A b c d e q n k =
      searsSum q n d e (A * q / (b * c)) (A * q / b) (A * q / c) (d * e * q⁻¹ ^ n / A) := by
  unfold searsSum watsonR4
  refine sum_congr rfl fun k _ => ?_
  ring

/-- The very-well-poised `₈φ₇` summand is symmetric under `(b,c,d,e) ↦ (d,e,b,c)`. -/
lemma watsonR8_swap (A b c d e q : ℂ) (n k : ℕ) :
    watsonR8 A b c d e q n k = watsonR8 A d e b c q n k := by
  unfold watsonR8; ring_nf

/-- The very-well-poised `₈φ₇` summand is symmetric under `(b,c,d,e) ↦ (b,e,c,d)`. -/
lemma watsonR8_cycle (A b c d e q : ℂ) (n k : ℕ) :
    watsonR8 A b c d e q n k = watsonR8 A b e c d q n k := by
  unfold watsonR8; ring_nf

/-- Comparison of two pairings of Watson's transformation on a punctured neighbourhood of the
very-well-poised parameter, in cleared form. -/
lemma eventually_pairings {b c d e b' c' d' e' q : ℂ} (A₀ : ℂ) (n : ℕ) (hb : b ≠ 0)
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hb' : b' ≠ 0) (hc' : c' ≠ 0) (hd' : d' ≠ 0)
    (he' : e' ≠ 0) (hq : q ≠ 0) (hqn : ‖q‖ < 1)
    (hsym : ∀ A : ℂ, ∀ k, watsonR8 A b c d e q n k = watsonR8 A b' c' d' e' q n k) :
    ∀ᶠ A in 𝓝[≠] A₀,
      qPochhammer (A * q / (d * e)) q n * qPochhammer (A * q / d') q n *
          qPochhammer (A * q / e') q n * ∑ k ∈ range (n + 1), watsonR4 A b c d e q n k =
        qPochhammer (A * q / (d' * e')) q n * qPochhammer (A * q / d) q n *
          qPochhammer (A * q / e) q n * ∑ k ∈ range (n + 1), watsonR4 A b' c' d' e' q n k := by
  have hqq : ∀ m ≤ n, qPochhammer q q m ≠ 0 := fun m _ => qPochhammer_self_ne_zero hqn m
  have ev : ∀ x : ℂ, x ≠ 0 → ∀ᶠ A in 𝓝[≠] A₀, qPochhammer (A * q / x) q n ≠ 0 := by
    intro x hx
    filter_upwards [eventually_qPochhammer_mul_ne_zero (div_ne_zero hq hx) hq A₀ n] with A hA
    rwa [mul_div_assoc]
  filter_upwards [eventually_ne A₀ 0, eventually_qPochhammer_mul_ne_zero hq hq A₀ (n + n),
    ev b hb, ev c hc, ev d hd, ev e he, ev b' hb', ev c' hc', ev d' hd', ev e' he',
    eventually_qPochhammer_div_ne_zero (d * e * q⁻¹ ^ n) q A₀ n,
    eventually_qPochhammer_div_ne_zero (d' * e' * q⁻¹ ^ n) q A₀ n]
    with A hA haq hB hC hD hE hB' hC' hD' hE' hY hY'
  have W1 := watsonR_of_ne n hA hb hc hd he hq hqq haq hB hC hD hE hY
  have W2 := watsonR_of_ne n hA hb' hc' hd' he' hq hqq haq hB' hC' hD' hE' hY'
  rw [sum_congr rfl fun k _ => hsym A k, W2] at W1
  have hn : qPochhammer (A * q) q n ≠ 0 := qPochhammer_ne_zero_of_le haq (by omega)
  field_simp at W1
  linear_combination -W1

/-- Continuity of a terminating `₄φ₃` sum in its parameters, away from vanishing denominators. -/
lemma continuousAt_searsSum {x₁ x₂ x₃ y₁ y₂ y₃ : ℂ → ℂ} {a q : ℂ} (n : ℕ) (hqn : ‖q‖ < 1)
    (hx₁ : ContinuousAt x₁ a) (hx₂ : ContinuousAt x₂ a) (hx₃ : ContinuousAt x₃ a)
    (hy₁ : ContinuousAt y₁ a) (hy₂ : ContinuousAt y₂ a) (hy₃ : ContinuousAt y₃ a)
    (h₁ : qPochhammer (y₁ a) q n ≠ 0) (h₂ : qPochhammer (y₂ a) q n ≠ 0)
    (h₃ : qPochhammer (y₃ a) q n ≠ 0) :
    ContinuousAt (fun t => searsSum q n (x₁ t) (x₂ t) (x₃ t) (y₁ t) (y₂ t) (y₃ t)) a := by
  have cP : ∀ {x : ℂ → ℂ}, ContinuousAt x a → ∀ k,
      ContinuousAt (fun t => qPochhammer (x t) q k) a :=
    fun hx k => (continuous_qPochhammer q k).continuousAt.comp hx
  unfold searsSum
  refine tendsto_finsetSum _ fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  refine ContinuousAt.mul (ContinuousAt.div ?_ ?_ ?_) continuousAt_const
  · exact (((continuousAt_const.mul (cP hx₁ k)).mul (cP hx₂ k)).mul (cP hx₃ k))
  · exact (((cP hy₁ k).mul (cP hy₂ k)).mul (cP hy₃ k)).mul continuousAt_const
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (qPochhammer_ne_zero_of_le h₁ hkn)
      (qPochhammer_ne_zero_of_le h₂ hkn)) (qPochhammer_ne_zero_of_le h₃ hkn))
      (qPochhammer_self_ne_zero hqn k)

/-- Continuity of a terminating `₃φ₂` sum in its parameters, away from vanishing denominators. -/
lemma continuousAt_phiSum {x₁ x₂ y₁ y₂ z : ℂ → ℂ} {a q : ℂ} (n : ℕ) (hqn : ‖q‖ < 1)
    (hx₁ : ContinuousAt x₁ a) (hx₂ : ContinuousAt x₂ a) (hy₁ : ContinuousAt y₁ a)
    (hy₂ : ContinuousAt y₂ a) (hz : ContinuousAt z a)
    (h₁ : qPochhammer (y₁ a) q n ≠ 0) (h₂ : qPochhammer (y₂ a) q n ≠ 0) :
    ContinuousAt (fun t => phiSum q n (x₁ t) (x₂ t) (y₁ t) (y₂ t) (z t)) a := by
  have cP : ∀ {x : ℂ → ℂ}, ContinuousAt x a → ∀ k,
      ContinuousAt (fun t => qPochhammer (x t) q k) a :=
    fun hx k => (continuous_qPochhammer q k).continuousAt.comp hx
  unfold phiSum
  refine tendsto_finsetSum _ fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  refine ContinuousAt.mul (ContinuousAt.div ?_ ?_ ?_) (hz.pow k)
  · exact ((continuousAt_const.mul (cP hx₁ k)).mul (cP hx₂ k))
  · exact ((cP hy₁ k).mul (cP hy₂ k)).mul continuousAt_const
  · exact mul_ne_zero (mul_ne_zero (qPochhammer_ne_zero_of_le h₁ hkn)
      (qPochhammer_ne_zero_of_le h₂ hkn)) (qPochhammer_self_ne_zero hqn k)

end SearsTransformation

open SearsTransformation

/-- `searsSum` is symmetric in its upper parameters. -/
lemma searsSum_comm_upper (q : ℂ) (n : ℕ) (x₁ x₂ x₃ y₁ y₂ y₃ : ℂ) :
    searsSum q n x₁ x₂ x₃ y₁ y₂ y₃ = searsSum q n x₃ x₁ x₂ y₁ y₂ y₃ := by
  unfold searsSum; exact sum_congr rfl fun k _ => by ring

/-- `searsSum` is symmetric in its lower parameters. -/
lemma searsSum_comm_lower (q : ℂ) (n : ℕ) (x₁ x₂ x₃ y₁ y₂ y₃ : ℂ) :
    searsSum q n x₁ x₂ x₃ y₁ y₂ y₃ = searsSum q n x₁ x₂ x₃ y₃ y₁ y₂ := by
  unfold searsSum; exact sum_congr rfl fun k _ => by ring

/-- Sears' transformation of a terminating balanced `₄φ₃`, cleared of denominators:
`(e,f,ef/(abc);q)_n ₄φ₃(q⁻ⁿ,a,b,c;d,e,f) =
(a,ef/(ab),ef/(ac);q)_n ₄φ₃(q⁻ⁿ,e/a,f/a,ef/(abc);ef/(ab),ef/(ac),q^{1-n}/a)` (DLMF 17.9.14). -/
theorem searsSum_transformation_second {a b c d e f q : ℂ} (n : ℕ) (hq : q ≠ 0)
    (hqn : ‖q‖ < 1) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hf : f ≠ 0) (hbal : d * e * f = a * b * c * q * q⁻¹ ^ n)
    (hD : qPochhammer d q n ≠ 0) (hE : qPochhammer e q n ≠ 0) (hF : qPochhammer f q n ≠ 0)
    (h₁ : qPochhammer (e * f / (a * b)) q n ≠ 0) (h₂ : qPochhammer (e * f / (a * c)) q n ≠ 0)
    (h₃ : qPochhammer (q * q⁻¹ ^ n / a) q n ≠ 0) :
    qPochhammer e q n * qPochhammer f q n * qPochhammer (e * f / (a * b * c)) q n *
        searsSum q n a b c d e f =
      qPochhammer a q n * qPochhammer (e * f / (a * b)) q n *
        qPochhammer (e * f / (a * c)) q n *
        searsSum q n (e / a) (f / a) (e * f / (a * b * c)) (e * f / (a * b)) (e * f / (a * c))
          (q * q⁻¹ ^ n / a) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, q⁻¹ ^ n = Q := ⟨_, rfl⟩
  have hQ0 : Q ≠ 0 := hQ ▸ pow_ne_zero _ (inv_ne_zero hq)
  rw [hQ] at hbal h₃ ⊢
  set A₀ := b * c * Q / d with hA₀
  have hfa : f / a ≠ 0 := div_ne_zero hf ha
  have hea : e / a ≠ 0 := div_ne_zero he ha
  have E := eventually_pairings A₀ n hfa hea hb hc hb hc hfa hea hq hqn
    (fun A k => watsonR8_swap A (f / a) (e / a) b c q n k)
  -- the parameters at `A₀`
  have p1 : A₀ * q / (f / a) = e := by
    rw [hA₀]; field_simp; linear_combination (-1) * hbal
  have p2 : A₀ * q / (e / a) = f := by
    rw [hA₀]; field_simp; linear_combination (-1) * hbal
  have p3 : A₀ * q / (f / a * (e / a)) = a := by
    rw [hA₀]; field_simp; linear_combination (-1) * hbal
  have p4 : b * c * Q / A₀ = d := by rw [hA₀]; field_simp
  have p5 : A₀ * q / (b * c) = e * f / (a * b * c) := by
    rw [hA₀]; field_simp; linear_combination (-1) * hbal
  have p6 : A₀ * q / b = e * f / (a * b) := by
    rw [hA₀]; field_simp; linear_combination (-1) * hbal
  have p7 : A₀ * q / c = e * f / (a * c) := by
    rw [hA₀]; field_simp; linear_combination (-1) * hbal
  have p8 : f / a * (e / a) * Q / A₀ = q * Q / a := by
    rw [hA₀]; field_simp; linear_combination hbal
  have key := eq_of_eventually_punctured (a := A₀) ?_ ?_ E
  · simp only [sum_watsonR4] at key
    rw [hQ] at key
    simp only [p1, p2, p3, p4, p5, p6, p7, p8] at key
    have s1 : searsSum q n b c a e f d = searsSum q n a b c d e f := by
      unfold searsSum; exact sum_congr rfl fun k _ => by ring
    have s2 : searsSum q n (f / a) (e / a) (e * f / (a * b * c)) (e * f / (a * b))
        (e * f / (a * c)) (q * Q / a) = searsSum q n (e / a) (f / a) (e * f / (a * b * c))
        (e * f / (a * b)) (e * f / (a * c)) (q * Q / a) := by
      unfold searsSum; exact sum_congr rfl fun k _ => by ring
    rw [s1, s2] at key
    linear_combination key
  · have hA0 : A₀ ≠ 0 := by rw [hA₀]; exact div_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hQ0) hd
    have cP : ∀ x : ℂ, ContinuousAt (fun A : ℂ => qPochhammer (A * q / x) q n) A₀ :=
      fun x => (continuous_qPochhammer q n).continuousAt.comp (by fun_prop)
    simp only [sum_watsonR4]
    refine ((cP _).mul (cP _)).mul (cP _) |>.mul (continuousAt_searsSum n hqn ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_)
    all_goals try fun_prop
    · show qPochhammer (A₀ * q / (f / a)) q n ≠ 0; rw [p1]; exact hE
    · show qPochhammer (A₀ * q / (e / a)) q n ≠ 0; rw [p2]; exact hF
    · show qPochhammer (b * c * q⁻¹ ^ n / A₀) q n ≠ 0; rw [hQ, p4]; exact hD
  · have hA0 : A₀ ≠ 0 := by rw [hA₀]; exact div_ne_zero (mul_ne_zero (mul_ne_zero hb hc) hQ0) hd
    have cP : ∀ x : ℂ, ContinuousAt (fun A : ℂ => qPochhammer (A * q / x) q n) A₀ :=
      fun x => (continuous_qPochhammer q n).continuousAt.comp (by fun_prop)
    simp only [sum_watsonR4]
    refine ((cP _).mul (cP _)).mul (cP _) |>.mul (continuousAt_searsSum n hqn ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_)
    all_goals try fun_prop
    · show qPochhammer (A₀ * q / b) q n ≠ 0; rw [p6]; exact h₁
    · show qPochhammer (A₀ * q / c) q n ≠ 0; rw [p7]; exact h₂
    · show qPochhammer (f / a * (e / a) * q⁻¹ ^ n / A₀) q n ≠ 0; rw [hQ, p8]; exact h₃

namespace SearsTransformation

/-- `q^(1-n) = q q⁻ⁿ` for `q ≠ 0`. -/
lemma zpow_one_sub_natCast {q : ℂ} (hq : q ≠ 0) (n : ℕ) : q ^ (1 - (n : ℤ)) = q * q⁻¹ ^ n := by
  rw [zpow_sub₀ hq, zpow_one, zpow_natCast, inv_pow, div_eq_mul_inv]

/-- Reversal in the form `(x;q)_n = (q q⁻ⁿ/x;q)_n (-x)ⁿ q^(n(n-1)/2)`. -/
lemma qPochhammer_reverse' {x q : ℂ} (hx : x ≠ 0) (hq : q ≠ 0) (n : ℕ) :
    qPochhammer x q n = qPochhammer (q * q⁻¹ ^ n / x) q n * (-x) ^ n * q ^ n.choose 2 := by
  rw [qPochhammer_reverse hx hq, zpow_one_sub_natCast hq]

end SearsTransformation

/-- Sears' transformation of a terminating balanced `₄φ₃`, cleared of denominators:
`(e,f;q)_n ₄φ₃(q⁻ⁿ,a,b,c;d,e,f) = aⁿ (e/a,f/a;q)_n ₄φ₃(q⁻ⁿ,a,d/b,d/c;d,aq^{1-n}/e,aq^{1-n}/f)`
(DLMF 17.9.14). -/
theorem searsSum_transformation_first {a b c d e f q : ℂ} (n : ℕ) (hq : q ≠ 0)
    (hqn : ‖q‖ < 1) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hf : f ≠ 0) (hbal : d * e * f = a * b * c * q * q⁻¹ ^ n)
    (hD : qPochhammer d q n ≠ 0) (hE : qPochhammer e q n ≠ 0) (hF : qPochhammer f q n ≠ 0)
    (h₁ : qPochhammer (a * q * q⁻¹ ^ n / e) q n ≠ 0)
    (h₂ : qPochhammer (a * q * q⁻¹ ^ n / f) q n ≠ 0) :
    qPochhammer e q n * qPochhammer f q n * searsSum q n a b c d e f =
      a ^ n * qPochhammer (e / a) q n * qPochhammer (f / a) q n *
        searsSum q n a (d / b) (d / c) d (a * q * q⁻¹ ^ n / e) (a * q * q⁻¹ ^ n / f) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, q⁻¹ ^ n = Q := ⟨_, rfl⟩
  have hQ0 : Q ≠ 0 := hQ ▸ pow_ne_zero _ (inv_ne_zero hq)
  have hrevf := qPochhammer_reverse' hf hq n
  have hrevfa := qPochhammer_reverse' (div_ne_zero hf ha) hq n
  rw [hQ] at hbal h₁ h₂ hrevf hrevfa ⊢
  set A₀ := d * e / (c * q) with hA₀
  have hec : e / c ≠ 0 := div_ne_zero he hc
  have hdc : d / c ≠ 0 := div_ne_zero hd hc
  have E := eventually_pairings A₀ n hec hdc ha hb hec hb hdc ha hq hqn
    (fun A k => watsonR8_cycle A (e / c) (d / c) a b q n k)
  have E' : ∀ᶠ A in 𝓝[≠] A₀,
      qPochhammer (A * q / (a * b)) q n * qPochhammer (A * q / (d / c)) q n *
          ∑ k ∈ range (n + 1), watsonR4 A (e / c) (d / c) a b q n k =
        qPochhammer (A * q / (d / c * a)) q n * qPochhammer (A * q / b) q n *
          ∑ k ∈ range (n + 1), watsonR4 A (e / c) b (d / c) a q n k := by
    filter_upwards [E, eventually_qPochhammer_mul_ne_zero (div_ne_zero hq ha) hq A₀ n]
      with A hA hne
    rw [← mul_div_assoc] at hne
    apply mul_left_cancel₀ hne
    linear_combination hA
  -- the parameters at `A₀`
  have p1 : A₀ * q / (e / c * (d / c)) = c := by rw [hA₀]; field_simp
  have p2 : A₀ * q / (e / c) = d := by rw [hA₀]; field_simp
  have p3 : A₀ * q / (d / c) = e := by rw [hA₀]; field_simp
  have p4 : a * b * Q / A₀ = f := by
    rw [hA₀]; field_simp; linear_combination (-1) * hbal
  have p5 : A₀ * q / (a * b) = q * Q / f := by
    rw [hA₀]; field_simp; linear_combination hbal
  have p6 : A₀ * q / (d / c * a) = e / a := by rw [hA₀]; field_simp
  have p7 : A₀ * q / b = a * q * Q / f := by
    rw [hA₀]; field_simp; linear_combination hbal
  have p8 : A₀ * q / (e / c * b) = d / b := by rw [hA₀]; field_simp
  have p9 : d / c * a * Q / A₀ = a * q * Q / e := by rw [hA₀]; field_simp
  have hA0 : A₀ ≠ 0 := by rw [hA₀]; exact div_ne_zero (mul_ne_zero hd he) (mul_ne_zero hc hq)
  have cP : ∀ x : ℂ, ContinuousAt (fun A : ℂ => qPochhammer (A * q / x) q n) A₀ :=
    fun x => (continuous_qPochhammer q n).continuousAt.comp (by fun_prop)
  have key := eq_of_eventually_punctured (a := A₀) ?_ ?_ E'
  · simp only [sum_watsonR4] at key
    rw [hQ] at key
    simp only [p1, p2, p3, p4, p5, p6, p7, p8, p9] at key
    have s2 : searsSum q n (d / c) a (d / b) d (a * q * Q / f) (a * q * Q / e) =
        searsSum q n a (d / b) (d / c) d (a * q * Q / e) (a * q * Q / f) := by
      unfold searsSum; exact sum_congr rfl fun k _ => by ring
    rw [s2] at key
    have hqf : qPochhammer (q * Q / f) q n ≠ 0 := by
      intro h0; rw [h0] at hrevf; simp [hrevf] at hF
    apply mul_left_cancel₀ hqf
    rw [hrevf, hrevfa, show q * Q / (f / a) = a * q * Q / f by field_simp]
    have hpow : a ^ n * (-(f / a)) ^ n = (-f) ^ n := by
      rw [← mul_pow]; congr 1; field_simp
    linear_combination (qPochhammer (q * Q / f) q n * (-f) ^ n * q ^ n.choose 2) * key -
      (qPochhammer (q * Q / f) q n * qPochhammer (e / a) q n * qPochhammer (a * q * Q / f) q n *
        q ^ n.choose 2 * searsSum q n a (d / b) (d / c) d (a * q * Q / e) (a * q * Q / f)) * hpow
  · simp only [sum_watsonR4]
    refine ((cP _).mul (cP _)).mul (continuousAt_searsSum n hqn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    all_goals try fun_prop
    · show qPochhammer (A₀ * q / (e / c)) q n ≠ 0; rw [p2]; exact hD
    · show qPochhammer (A₀ * q / (d / c)) q n ≠ 0; rw [p3]; exact hE
    · show qPochhammer (a * b * q⁻¹ ^ n / A₀) q n ≠ 0; rw [hQ, p4]; exact hF
  · simp only [sum_watsonR4]
    refine ((cP _).mul (cP _)).mul (continuousAt_searsSum n hqn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
    all_goals try fun_prop
    · show qPochhammer (A₀ * q / (e / c)) q n ≠ 0; rw [p2]; exact hD
    · show qPochhammer (A₀ * q / b) q n ≠ 0; rw [p7]; exact h₂
    · show qPochhammer (d / c * a * q⁻¹ ^ n / A₀) q n ≠ 0; rw [hQ, p9]; exact h₁

/-- The terminating `₄φ₃(q⁻ⁿ,x₁,x₂,x₃;y₁,y₂,y₃;q,q)` is the finite sum `searsSum`. -/
theorem qPhi_four_three_eq_searsSum {q : ℂ} (hq : q ≠ 0) (n : ℕ) (x₁ x₂ x₃ y₁ y₂ y₃ : ℂ) :
    qPhi [q ^ (-(n : ℤ)), x₁, x₂, x₃] [y₁, y₂, y₃] q q = searsSum q n x₁ x₂ x₃ y₁ y₂ y₃ := by
  rw [qPhi_terminates hq n, qPhiPartial, searsSum]
  refine sum_congr rfl fun k _ => ?_
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, List.length_cons, List.length_nil]
  rw [zpow_neg, zpow_natCast, inv_pow]
  norm_num
  left; ring

/-- The terminating `₃φ₂(q⁻ⁿ,x₁,x₂;y₁,y₂;q,q)` is a `searsSum` with a cancelling pair of
zero parameters. -/
theorem qPhi_three_two_eq_searsSum {q : ℂ} (hq : q ≠ 0) (n : ℕ) (x₁ x₂ y₁ y₂ : ℂ) :
    qPhi [q ^ (-(n : ℤ)), x₁, x₂] [y₁, y₂] q q = searsSum q n x₁ x₂ 0 y₁ y₂ 0 := by
  rw [qPhi_terminates hq n, qPhiPartial, searsSum]
  refine sum_congr rfl fun k _ => ?_
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, List.length_cons, List.length_nil, qPochhammer_zero_param]
  rw [zpow_neg, zpow_natCast, inv_pow]
  norm_num
  left; ring

/-- The terminating `₃φ₂(q⁻ⁿ,x₁,x₂;y₁,y₂;q,z)` is the finite sum `phiSum`. -/
theorem qPhi_three_two_eq_phiSum {q : ℂ} (hq : q ≠ 0) (n : ℕ) (x₁ x₂ y₁ y₂ z : ℂ) :
    qPhi [q ^ (-(n : ℤ)), x₁, x₂] [y₁, y₂] q z = phiSum q n x₁ x₂ y₁ y₂ z := by
  rw [qPhi_terminates hq n, qPhiPartial, phiSum]
  refine sum_congr rfl fun k _ => ?_
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, List.length_cons, List.length_nil]
  rw [zpow_neg, zpow_natCast, inv_pow]
  norm_num
  left; ring

/-- The terminating `₂φ₁(q⁻ⁿ,x₁;y₁;q,z)` is a `phiSum` with a cancelling pair of zero
parameters. -/
theorem qPhi_two_one_eq_phiSum {q : ℂ} (hq : q ≠ 0) (n : ℕ) (x₁ y₁ z : ℂ) :
    qPhi [q ^ (-(n : ℤ)), x₁] [y₁] q z = phiSum q n x₁ 0 y₁ 0 z := by
  rw [qPhi_terminates hq n, qPhiPartial, phiSum]
  refine sum_congr rfl fun k _ => ?_
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, List.length_cons, List.length_nil, qPochhammer_zero_param]
  rw [zpow_neg, zpow_natCast, inv_pow]
  norm_num

/-- The terminating `₃φ₁(q⁻ⁿ,x₁,x₂;y₁;q,w)`, with its phase factor, as a finite sum. -/
theorem qPhi_three_one_eq_sum {q : ℂ} (hq : q ≠ 0) (n : ℕ) (x₁ x₂ y₁ w : ℂ) :
    qPhi [q ^ (-(n : ℤ)), x₁, x₂] [y₁] q w =
      ∑ k ∈ range (n + 1), qPochhammer (q⁻¹ ^ n) q k * qPochhammer x₁ q k *
        qPochhammer x₂ q k / (qPochhammer y₁ q k * qPochhammer q q k) *
        (w ^ k / ((-1) ^ k * q ^ k.choose 2)) := by
  rw [qPhi_terminates hq n, qPhiPartial]
  refine sum_congr rfl fun k _ => ?_
  have ht : DLMF.QSeries.TripleProduct.tri (k : ℤ) = (k.choose 2 : ℤ) := by
    simpa using (DLMF.QSeries.TripleProduct.tri_sub_cast k 0).symm
  simp only [qPhiTerm, qPhiExponent, qPochhammerList, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, List.length_cons, List.length_nil, ht, mul_one]
  rw [zpow_neg, zpow_natCast, inv_pow, zpow_natCast]
  norm_num
  ring

/-- A lower parameter regular in the sense of `QDenominatorRegular` has nonzero factorials. -/
lemma qPochhammer_ne_zero_of_mem_qDenominatorRegular {b : List ℂ} {x q : ℂ} (hq : ‖q‖ < 1)
    (hb : QDenominatorRegular b q) (hx : x ∈ b) (n : ℕ) : qPochhammer x q n ≠ 0 :=
  qPochhammer_ne_zero_of_factors hq (fun j h => hb x hx j (sub_eq_zero.mp h).symm) n


namespace SearsTransformation

/-- `tⁿ (e/t;q)_n = ∏_{j<n} (t - e q^j)` for `t ≠ 0`. -/
lemma pow_mul_qPochhammer_div {t e q : ℂ} (ht : t ≠ 0) (n : ℕ) :
    t ^ n * qPochhammer (e / t) q n = ∏ j ∈ range n, (t - e * q ^ j) := by
  rw [qPochhammer_eq_prod, ← card_range n, ← prod_const, card_range, ← prod_mul_distrib]
  exact prod_congr rfl fun j _ => by field_simp

/-- `∏_{j<n} (-e q^j) = (-e)ⁿ q^(n(n-1)/2)`. -/
lemma prod_neg_mul_pow (e q : ℂ) (n : ℕ) :
    ∏ j ∈ range n, (0 - e * q ^ j) = (-e) ^ n * q ^ n.choose 2 := by
  simp only [zero_sub, neg_mul_eq_neg_mul, prod_mul_distrib, prod_const, card_range]
  rw [prod_pow_eq_pow_sum, sum_range_id, Nat.choose_two_right]

end SearsTransformation

/-- The terminating `₃φ₂` transformation
`(e;q)_n ₃φ₂(q⁻ⁿ,b,c;d,e;q,q) = (bc/d)ⁿ (de/(bc);q)_n ₃φ₂(q⁻ⁿ,d/b,d/c;d,de/(bc);q,q)`, cleared of
denominators, as the limit `a → 0` of Sears' transformation (DLMF 17.9.8). -/
theorem searsSum_three_two_first {b c d e q : ℂ} (n : ℕ) (hq : q ≠ 0) (hqn : ‖q‖ < 1)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hD : qPochhammer d q n ≠ 0)
    (hE : qPochhammer e q n ≠ 0) (hM : qPochhammer (d * e / (b * c)) q n ≠ 0) :
    qPochhammer e q n * searsSum q n b c 0 d e 0 =
      (b * c / d) ^ n * qPochhammer (d * e / (b * c)) q n *
        searsSum q n (d / b) (d / c) 0 d (d * e / (b * c)) 0 := by
  have cP : ∀ {x : ℂ → ℂ} {a : ℂ}, ContinuousAt x a →
      ContinuousAt (fun t => qPochhammer (x t) q n) a :=
    fun hx => (continuous_qPochhammer q n).continuousAt.comp hx
  -- the case `e ≠ 0`, as a limit of Sears' transformation
  have main : ∀ e : ℂ, e ≠ 0 → qPochhammer e q n ≠ 0 → qPochhammer (d * e / (b * c)) q n ≠ 0 →
      qPochhammer e q n * searsSum q n b c 0 d e 0 =
        (b * c / d) ^ n * qPochhammer (d * e / (b * c)) q n *
          searsSum q n (d / b) (d / c) 0 d (d * e / (b * c)) 0 := by
    intro e he hE hM
    obtain ⟨Q, hQ⟩ : ∃ Q, q⁻¹ ^ n = Q := ⟨_, rfl⟩
    have hQ0 : Q ≠ 0 := hQ ▸ pow_ne_zero _ (inv_ne_zero hq)
    have hrev := qPochhammer_reverse' (div_ne_zero (mul_ne_zero hd he) (mul_ne_zero hb hc)) hq n
    rw [hQ] at hrev
    set κ := b * c * q * Q / (d * e) with hκ
    set μ := d * e / (b * c) with hμ
    have hκμ : q * Q / μ = κ := by rw [hμ, hκ]; field_simp
    rw [hκμ] at hrev
    have hκ0 : κ ≠ 0 := by
      rw [hκ]; exact div_ne_zero (by simp [*]) (mul_ne_zero hd he)
    have hqQe : q * Q / e ≠ 0 := div_ne_zero (mul_ne_zero hq hQ0) he
    set L : ℂ → ℂ := fun t => qPochhammer e q n * qPochhammer (t * κ) q n *
      searsSum q n t b c d e (t * κ) with hL
    set R : ℂ → ℂ := fun t => (∏ j ∈ range n, (t - e * q ^ j)) * qPochhammer κ q n *
      searsSum q n t (d / b) (d / c) d (t * (q * Q / e)) μ with hR
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L t = R t := by
      filter_upwards [self_mem_nhdsWithin, eventually_qPochhammer_mul_ne_zero hκ0 hq 0 n,
        eventually_qPochhammer_mul_ne_zero hqQe hq 0 n] with t ht0 hF h₁
      have ht : t ≠ 0 := ht0
      have hbal : d * e * (t * κ) = t * b * c * q * q⁻¹ ^ n := by rw [hQ, hκ]; field_simp
      have h₁' : qPochhammer (t * q * q⁻¹ ^ n / e) q n ≠ 0 := by
        rwa [hQ, mul_assoc t, mul_div_assoc]
      have h₂' : qPochhammer (t * q * q⁻¹ ^ n / (t * κ)) q n ≠ 0 := by
        rwa [hQ, show t * q * Q / (t * κ) = μ by rw [hκ, hμ]; field_simp]
      have H := searsSum_transformation_first n hq hqn ht hb hc hd he (mul_ne_zero ht hκ0) hbal
        hD hE hF h₁' h₂'
      rw [hQ, show t * κ / t = κ by field_simp, show t * q * Q / (t * κ) = μ by
        rw [hκ, hμ]; field_simp, show t * q * Q / e = t * (q * Q / e) by ring,
        mul_assoc (t ^ n), ← mul_assoc (t ^ n), pow_mul_qPochhammer_div ht] at H
      simp only [hL, hR]
      linear_combination H
    have key := eq_of_eventually_punctured (a := 0) ?_ ?_ hev
    · simp only [hL, hR, zero_mul, prod_neg_mul_pow, qPochhammer_zero_param] at key
      have s1 : searsSum q n 0 b c d e 0 = searsSum q n b c 0 d e 0 := by
        unfold searsSum; exact sum_congr rfl fun k _ => by ring
      have s2 : searsSum q n 0 (d / b) (d / c) d 0 μ = searsSum q n (d / b) (d / c) 0 d μ 0 := by
        unfold searsSum; exact sum_congr rfl fun k _ => by ring
      have hp : (b * c / d) ^ n * (-μ) ^ n = (-e) ^ n := by
        rw [← mul_pow, hμ]; congr 1; field_simp
      rw [s1, s2] at key
      linear_combination key - (b * c / d) ^ n * searsSum q n (d / b) (d / c) 0 d μ 0 * hrev -
        qPochhammer κ q n * q ^ n.choose 2 * searsSum q n (d / b) (d / c) 0 d μ 0 * hp
    · refine (continuousAt_const.mul (cP (by fun_prop))).mul
        (continuousAt_searsSum n hqn ?_ ?_ ?_ ?_ ?_ ?_ hD hE ?_)
      all_goals try fun_prop
      simp [qPochhammer_zero_param]
    · refine (ContinuousAt.mul (by fun_prop) continuousAt_const).mul
        (continuousAt_searsSum n hqn ?_ ?_ ?_ ?_ ?_ ?_ hD ?_ hM)
      all_goals try fun_prop
      simp [qPochhammer_zero_param]
  by_cases he : e = 0
  · -- the case `e = 0`, by continuity in `e`
    subst he
    set L : ℂ → ℂ := fun t => qPochhammer t q n * searsSum q n b c 0 d t 0 with hL
    set R : ℂ → ℂ := fun t => (b * c / d) ^ n * qPochhammer (d * t / (b * c)) q n *
      searsSum q n (d / b) (d / c) 0 d (d * t / (b * c)) 0 with hR
    have hdbc : d / (b * c) ≠ 0 := div_ne_zero hd (mul_ne_zero hb hc)
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L t = R t := by
      filter_upwards [self_mem_nhdsWithin, eventually_qPochhammer_mul_ne_zero one_ne_zero hq 0 n,
        eventually_qPochhammer_mul_ne_zero hdbc hq 0 n] with t ht0 h1 h2
      rw [mul_one] at h1
      rw [← mul_div_assoc, mul_comm t d] at h2
      exact main t ht0 h1 h2
    have key := eq_of_eventually_punctured (a := 0) ?_ ?_ hev
    · simpa [hL, hR] using key
    · exact (cP continuousAt_id).mul (continuousAt_searsSum n hqn (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hD (by simp)
        (by simp [qPochhammer_zero_param]))
    · exact (continuousAt_const.mul (cP (by fun_prop))).mul (continuousAt_searsSum n hqn
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hD
        (by simp) (by simp [qPochhammer_zero_param]))
  · exact main e he hE hM
/-- The terminating `₃φ₂` transformation
`(d,e;q)_n ₃φ₂(q⁻ⁿ,b,c;d,e;q,q) =
cⁿ (e/c,d/c;q)_n ₃φ₂(q⁻ⁿ,c,cbq^{1-n}/(de);cq^{1-n}/e,cq^{1-n}/d;q,q)`, cleared of denominators,
as a limit of Sears' transformation (DLMF 17.9.11). -/
theorem searsSum_three_two_fourth {b c d e q : ℂ} (n : ℕ) (hq : q ≠ 0) (hqn : ‖q‖ < 1)
    (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0) (hD : qPochhammer d q n ≠ 0)
    (hE : qPochhammer e q n ≠ 0) (h₁ : qPochhammer (c * q * q⁻¹ ^ n / e) q n ≠ 0)
    (h₂ : qPochhammer (c * q * q⁻¹ ^ n / d) q n ≠ 0) :
    qPochhammer e q n * qPochhammer d q n * searsSum q n b c 0 d e 0 =
      c ^ n * qPochhammer (e / c) q n * qPochhammer (d / c) q n *
        searsSum q n c (c * b * q * q⁻¹ ^ n / (d * e)) 0 (c * q * q⁻¹ ^ n / e)
          (c * q * q⁻¹ ^ n / d) 0 := by
  have cP : ∀ {x : ℂ → ℂ} {a : ℂ}, ContinuousAt x a →
      ContinuousAt (fun t => qPochhammer (x t) q n) a :=
    fun hx => (continuous_qPochhammer q n).continuousAt.comp hx
  obtain ⟨Q, hQ⟩ : ∃ Q, q⁻¹ ^ n = Q := ⟨_, rfl⟩
  have hQ0 : Q ≠ 0 := hQ ▸ pow_ne_zero _ (inv_ne_zero hq)
  rw [hQ] at h₁ h₂ ⊢
  -- the case `b ≠ 0`, as the limit `C → 0` of Sears' transformation
  have main : ∀ b : ℂ, b ≠ 0 →
      qPochhammer e q n * qPochhammer d q n * searsSum q n b c 0 d e 0 =
        c ^ n * qPochhammer (e / c) q n * qPochhammer (d / c) q n *
          searsSum q n c (c * b * q * Q / (d * e)) 0 (c * q * Q / e) (c * q * Q / d) 0 := by
    intro b hb
    set κ := c * b * q * Q / (d * e) with hκ
    have hκ0 : κ ≠ 0 := by
      rw [hκ]; exact div_ne_zero (by simp [*]) (mul_ne_zero hd he)
    set L : ℂ → ℂ := fun t => qPochhammer e q n * qPochhammer d q n *
      searsSum q n c b t (t * κ) e d with hL
    set R : ℂ → ℂ := fun t => c ^ n * qPochhammer (e / c) q n * qPochhammer (d / c) q n *
      searsSum q n c (t * (κ / b)) κ (t * κ) (c * q * Q / e) (c * q * Q / d) with hR
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L t = R t := by
      filter_upwards [self_mem_nhdsWithin, eventually_qPochhammer_mul_ne_zero hκ0 hq 0 n]
        with t ht0 hT
      have ht : t ≠ 0 := ht0
      have hbal : t * κ * e * d = c * b * t * q * q⁻¹ ^ n := by rw [hQ, hκ]; field_simp
      rw [← hQ] at h₁ h₂
      have H := searsSum_transformation_first n hq hqn hc hb ht (mul_ne_zero ht hκ0) he hd hbal
        hT hE hD h₁ h₂
      rw [hQ, show t * κ / t = κ by field_simp, show t * κ / b = t * (κ / b) by ring] at H
      simp only [hL, hR]
      linear_combination H
    have key := eq_of_eventually_punctured (a := 0) ?_ ?_ hev
    · simp only [hL, hR, zero_mul] at key
      have s1 : searsSum q n c b 0 0 e d = searsSum q n b c 0 d e 0 := by
        unfold searsSum; exact sum_congr rfl fun k _ => by ring
      have s2 : searsSum q n c 0 κ 0 (c * q * Q / e) (c * q * Q / d) =
          searsSum q n c κ 0 (c * q * Q / e) (c * q * Q / d) 0 := by
        unfold searsSum; exact sum_congr rfl fun k _ => by ring
      rw [s1, s2] at key
      linear_combination key
    · refine continuousAt_const.mul
        (continuousAt_searsSum n hqn ?_ ?_ ?_ ?_ ?_ ?_ ?_ hE hD)
      all_goals try fun_prop
      simp [qPochhammer_zero_param]
    · refine continuousAt_const.mul
        (continuousAt_searsSum n hqn ?_ ?_ ?_ ?_ ?_ ?_ ?_ h₁ h₂)
      all_goals try fun_prop
      simp [qPochhammer_zero_param]
  by_cases hb : b = 0
  · -- the case `b = 0`, by continuity in `b`
    subst hb
    set L : ℂ → ℂ := fun t => qPochhammer e q n * qPochhammer d q n *
      searsSum q n t c 0 d e 0 with hL
    set R : ℂ → ℂ := fun t => c ^ n * qPochhammer (e / c) q n * qPochhammer (d / c) q n *
      searsSum q n c (c * t * q * Q / (d * e)) 0 (c * q * Q / e) (c * q * Q / d) 0 with hR
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L t = R t := by
      filter_upwards [self_mem_nhdsWithin] with t ht0
      exact main t ht0
    have key := eq_of_eventually_punctured (a := 0) ?_ ?_ hev
    · simpa [hL, hR] using key
    · exact continuousAt_const.mul (continuousAt_searsSum n hqn (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hD hE (by simp))
    · exact continuousAt_const.mul (continuousAt_searsSum n hqn (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) h₁ h₂ (by simp))
  · exact main b hb


/-- The terminating `₃φ₂` transformation
`(e;q)_n ₃φ₂(q⁻ⁿ,b,c;d,e;q,q) = cⁿ (e/c;q)_n ₃φ₂(q⁻ⁿ,c,d/b;d,cq^{1-n}/e;q,bq/e)`, cleared of
denominators, as a limit of Sears' transformation (DLMF 17.9.9). -/
theorem phiSum_three_two_second {b c d e q : ℂ} (n : ℕ) (hq : q ≠ 0) (hqn : ‖q‖ < 1)
    (hb : b ≠ 0) (hc : c ≠ 0) (he : e ≠ 0) (hD : qPochhammer d q n ≠ 0)
    (hE : qPochhammer e q n ≠ 0) (h₁ : qPochhammer (c * q * q⁻¹ ^ n / e) q n ≠ 0) :
    qPochhammer e q n * searsSum q n b c 0 d e 0 =
      c ^ n * qPochhammer (e / c) q n *
        phiSum q n c (d / b) d (c * q * q⁻¹ ^ n / e) (b * q / e) := by
  have cP : ∀ {x : ℂ → ℂ} {a : ℂ}, ContinuousAt x a →
      ContinuousAt (fun t => qPochhammer (x t) q n) a :=
    fun hx => (continuous_qPochhammer q n).continuousAt.comp hx
  obtain ⟨Q, hQ⟩ : ∃ Q, q⁻¹ ^ n = Q := ⟨_, rfl⟩
  have hQ0 : Q ≠ 0 := hQ ▸ pow_ne_zero _ (inv_ne_zero hq)
  rw [hQ] at h₁ ⊢
  -- the case `d ≠ 0`, as the limit `C → 0` of Sears' transformation
  have main : ∀ d : ℂ, d ≠ 0 → qPochhammer d q n ≠ 0 →
      qPochhammer e q n * searsSum q n b c 0 d e 0 =
        c ^ n * qPochhammer (e / c) q n * phiSum q n c (d / b) d (c * q * Q / e) (b * q / e) := by
    intro d hd hD
    set κ := c * b * q * Q / (d * e) with hκ
    set μ := d * e / b with hμ
    have hκ0 : κ ≠ 0 := by
      rw [hκ]; exact div_ne_zero (by simp [*]) (mul_ne_zero hd he)
    have hμ0 : μ ≠ 0 := by rw [hμ]; exact div_ne_zero (mul_ne_zero hd he) hb
    set α : ℕ → ℂ := fun k => qPochhammer Q q k * qPochhammer c q k * qPochhammer (d / b) q k /
      (qPochhammer d q k * qPochhammer (c * q * Q / e) q k * qPochhammer q q k) with hα
    set W : ℕ → ℂ → ℂ := fun k t => (∏ j ∈ range k, (t - d * q ^ j)) /
      ∏ j ∈ range k, (t - μ * q ^ j) with hW
    set L : ℂ → ℂ := fun t => qPochhammer e q n * qPochhammer (t * κ) q n *
      searsSum q n c b t d e (t * κ) with hL
    set R : ℂ → ℂ := fun t => c ^ n * qPochhammer (e / c) q n * qPochhammer (t * (κ / c)) q n *
      ∑ k ∈ range (n + 1), α k * W k t * q ^ k with hR
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L t = R t := by
      filter_upwards [self_mem_nhdsWithin, eventually_qPochhammer_mul_ne_zero hκ0 hq 0 n,
        eventually_qPochhammer_div_ne_zero μ q 0 n] with t ht0 hT hM
      have ht : t ≠ 0 := ht0
      have hbal : d * e * (t * κ) = c * b * t * q * q⁻¹ ^ n := by rw [hQ, hκ]; field_simp
      have hμt : c * q * Q / (t * κ) = μ / t := by rw [hκ, hμ]; field_simp
      have h₂ : qPochhammer (c * q * q⁻¹ ^ n / (t * κ)) q n ≠ 0 := by rwa [hQ, hμt]
      rw [← hQ] at h₁
      have H := searsSum_transformation_first n hq hqn hc hb ht hd he (mul_ne_zero ht hκ0) hbal
        hD hE hT h₁ h₂
      rw [hQ, hμt, show t * κ / c = t * (κ / c) by ring] at H
      have hS : searsSum q n c (d / b) (d / t) d (c * q * Q / e) (μ / t) =
          ∑ k ∈ range (n + 1), α k * W k t * q ^ k := by
        unfold searsSum
        refine sum_congr rfl fun k hk => ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
        have e1 := pow_mul_qPochhammer_div (e := d) (q := q) ht k
        have e2 := pow_mul_qPochhammer_div (e := μ) (q := q) ht k
        have hMk : qPochhammer (μ / t) q k ≠ 0 := qPochhammer_ne_zero_of_le hM hkn
        have htk : t ^ k ≠ 0 := pow_ne_zero _ ht
        simp only [hα, hW]
        rw [← e1, ← e2, mul_div_mul_left _ _ htk]
        rw [← hQ]
        field_simp
      rw [hS] at H
      simp only [hL, hR]
      linear_combination H
    have hW0 : ∀ k, W k 0 = (b / e) ^ k := by
      intro k
      simp only [hW, prod_neg_mul_pow]
      have : (-μ) ^ k ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr hμ0)
      rw [hμ, mul_div_mul_right _ _ (pow_ne_zero _ hq), ← div_pow]
      congr 1
      field_simp
    have key := eq_of_eventually_punctured (a := 0) ?_ ?_ hev
    · simp only [hL, hR, zero_mul, qPochhammer_zero_param, hW0] at key
      have s1 : searsSum q n c b 0 d e 0 = searsSum q n b c 0 d e 0 := by
        unfold searsSum; exact sum_congr rfl fun k _ => by ring
      have s2 : ∑ k ∈ range (n + 1), α k * (b / e) ^ k * q ^ k =
          phiSum q n c (d / b) d (c * q * Q / e) (b * q / e) := by
        unfold phiSum
        refine sum_congr rfl fun k _ => ?_
        simp only [hα]; rw [← hQ, mul_assoc, ← mul_pow, div_mul_eq_mul_div b e q]
      rw [s1, s2] at key
      linear_combination key
    · refine (continuousAt_const.mul (cP (by fun_prop))).mul
        (continuousAt_searsSum n hqn ?_ ?_ ?_ ?_ ?_ ?_ hD hE ?_)
      all_goals try fun_prop
      simp [qPochhammer_zero_param]
    · refine (continuousAt_const.mul (cP (by fun_prop))).mul
        (tendsto_finsetSum _ fun k _ => ?_)
      refine (continuousAt_const.mul (ContinuousAt.div (by fun_prop) (by fun_prop) ?_)).mul
        continuousAt_const
      rw [prod_neg_mul_pow]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hμ0)) (pow_ne_zero _ hq)
  by_cases hd : d = 0
  · -- the case `d = 0`, by continuity in `d`
    subst hd
    set L : ℂ → ℂ := fun t => qPochhammer e q n * searsSum q n b c 0 t e 0 with hL
    set R : ℂ → ℂ := fun t => c ^ n * qPochhammer (e / c) q n *
      phiSum q n c (t / b) t (c * q * Q / e) (b * q / e) with hR
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L t = R t := by
      filter_upwards [self_mem_nhdsWithin, eventually_qPochhammer_mul_ne_zero one_ne_zero hq 0 n]
        with t ht0 hT
      rw [mul_one] at hT
      exact main t ht0 hT
    have key := eq_of_eventually_punctured (a := 0) ?_ ?_ hev
    · simpa [hL, hR] using key
    · exact continuousAt_const.mul (continuousAt_searsSum n hqn (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hD hE (by simp))
    · exact continuousAt_const.mul (continuousAt_phiSum n hqn (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop) (by fun_prop) hD h₁)
  · exact main d hd hD


/-- The terminating `₃φ₂` transformation
`(e;q)_n ₃φ₂(q⁻ⁿ,b,c;d,e;q,deqⁿ/(bc)) = (e/c;q)_n ₃φ₂(q⁻ⁿ,c,d/b;d,cq^{1-n}/e;q,q)`, cleared of
denominators, as a limit of Sears' transformation (DLMF 17.9.10). -/
theorem phiSum_three_two_third {b c d e q : ℂ} (n : ℕ) (hq : q ≠ 0) (hqn : ‖q‖ < 1)
    (hb : b ≠ 0) (hc : c ≠ 0) (he : e ≠ 0) (hD : qPochhammer d q n ≠ 0)
    (hE : qPochhammer e q n ≠ 0) (h₁ : qPochhammer (c * q * q⁻¹ ^ n / e) q n ≠ 0) :
    qPochhammer e q n * phiSum q n b c d e (d * e * q ^ n / (b * c)) =
      qPochhammer (e / c) q n * searsSum q n c (d / b) 0 d (c * q * q⁻¹ ^ n / e) 0 := by
  have cP : ∀ {x : ℂ → ℂ} {a : ℂ}, ContinuousAt x a →
      ContinuousAt (fun t => qPochhammer (x t) q n) a :=
    fun hx => (continuous_qPochhammer q n).continuousAt.comp hx
  have hqn0 : q ^ n * q⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hq, one_pow]
  obtain ⟨Q, hQ⟩ : ∃ Q, q⁻¹ ^ n = Q := ⟨_, rfl⟩
  have hQ0 : Q ≠ 0 := hQ ▸ pow_ne_zero _ (inv_ne_zero hq)
  rw [hQ] at h₁ hqn0 ⊢
  -- the case `d ≠ 0`, as the limit `C → ∞` of Sears' transformation
  have main : ∀ d : ℂ, d ≠ 0 → qPochhammer d q n ≠ 0 →
      qPochhammer e q n * phiSum q n b c d e (d * e * q ^ n / (b * c)) =
        qPochhammer (e / c) q n * searsSum q n c (d / b) 0 d (c * q * Q / e) 0 := by
    intro d hd hD
    set κ := c * b * q * Q / (d * e) with hκ
    have hκ0 : κ ≠ 0 := by
      rw [hκ]; exact div_ne_zero (by simp [*]) (mul_ne_zero hd he)
    have hν0 : c * q * Q / κ ≠ 0 := div_ne_zero (by simp [*]) hκ0
    set β : ℕ → ℂ := fun k => qPochhammer Q q k * qPochhammer c q k * qPochhammer b q k /
      (qPochhammer d q k * qPochhammer e q k * qPochhammer q q k) with hβ
    set V : ℕ → ℂ → ℂ := fun k t => (∏ j ∈ range k, (t - 1 * q ^ j)) /
      ∏ j ∈ range k, (t - κ * q ^ j) with hV
    set L : ℂ → ℂ := fun t => qPochhammer e q n * (∏ j ∈ range n, (t - κ * q ^ j)) *
      ∑ k ∈ range (n + 1), β k * V k t * q ^ k with hL
    set R : ℂ → ℂ := fun t => qPochhammer (e / c) q n * (c ^ n *
      ∏ j ∈ range n, (t - κ / c * q ^ j)) *
      searsSum q n c (d / b) (d * t) d (c * q * Q / e) (t * (c * q * Q / κ)) with hR
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L t = R t := by
      filter_upwards [self_mem_nhdsWithin, eventually_qPochhammer_div_ne_zero κ q 0 n,
        eventually_qPochhammer_mul_ne_zero hν0 hq 0 n] with t ht0 hT hN
      have ht : t ≠ 0 := ht0
      have hbal : d * e * (κ / t) = c * b * (1 / t) * q * q⁻¹ ^ n := by
        rw [hQ, hκ]; field_simp
      have h₂ : qPochhammer (c * q * q⁻¹ ^ n / (κ / t)) q n ≠ 0 := by
        rwa [hQ, show c * q * Q / (κ / t) = t * (c * q * Q / κ) by field_simp]
      rw [← hQ] at h₁
      have H := searsSum_transformation_first n hq hqn hc hb (one_div_ne_zero ht) hd he
        (div_ne_zero hκ0 ht) hbal hD hE hT h₁ h₂
      rw [hQ, show c * q * Q / (κ / t) = t * (c * q * Q / κ) by field_simp,
        show d / (1 / t) = d * t by field_simp, show κ / t / c = κ / c / t by ring] at H
      have htn : t ^ n ≠ 0 := pow_ne_zero _ ht
      have hS : searsSum q n c b (1 / t) d e (κ / t) =
          ∑ k ∈ range (n + 1), β k * V k t * q ^ k := by
        unfold searsSum
        refine sum_congr rfl fun k hk => ?_
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
        have e1 := pow_mul_qPochhammer_div (e := 1) (q := q) ht k
        have e2 := pow_mul_qPochhammer_div (e := κ) (q := q) ht k
        have hTk : qPochhammer (κ / t) q k ≠ 0 := qPochhammer_ne_zero_of_le hT hkn
        have htk : t ^ k ≠ 0 := pow_ne_zero _ ht
        simp only [hβ, hV]
        rw [← e1, ← e2, mul_div_mul_left _ _ htk]
        rw [← hQ]
        field_simp
      rw [hS] at H
      have eL := pow_mul_qPochhammer_div (e := κ) (q := q) ht n
      have eR := pow_mul_qPochhammer_div (e := κ / c) (q := q) ht n
      simp only [hL, hR, ← eL, ← eR]
      linear_combination (t ^ n) * H
    have hV0 : ∀ k, V k 0 = (1 / κ) ^ k := by
      intro k
      simp only [hV, prod_neg_mul_pow]
      rw [mul_div_mul_right _ _ (pow_ne_zero _ hq), ← div_pow]
      congr 1
      field_simp
    have hP : (∏ j ∈ range n, (0 - κ * q ^ j)) ≠ 0 := by
      rw [prod_neg_mul_pow]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hκ0)) (pow_ne_zero _ hq)
    have key := eq_of_eventually_punctured (a := 0) ?_ ?_ hev
    · simp only [hL, hR, zero_mul, mul_zero, hV0] at key
      have hc0 : c ^ n * ∏ j ∈ range n, (0 - κ / c * q ^ j) = ∏ j ∈ range n, (0 - κ * q ^ j) := by
        rw [prod_neg_mul_pow, prod_neg_mul_pow, ← mul_assoc, ← mul_pow]
        congr 2; field_simp
      have s2 : ∑ k ∈ range (n + 1), β k * (1 / κ) ^ k * q ^ k =
          phiSum q n b c d e (d * e * q ^ n / (b * c)) := by
        unfold phiSum
        refine sum_congr rfl fun k _ => ?_
        have hz : d * e * q ^ n / (b * c) = 1 / κ * q := by
          rw [hκ]; field_simp; linear_combination hqn0
        simp only [hβ]; rw [← hQ, hz, mul_pow]; ring
      rw [hc0, s2] at key
      apply mul_left_cancel₀ hP
      linear_combination key
    · refine (continuousAt_const.mul (by fun_prop)).mul (tendsto_finsetSum _ fun k _ => ?_)
      refine (continuousAt_const.mul (ContinuousAt.div (by fun_prop) (by fun_prop) ?_)).mul
        continuousAt_const
      rw [prod_neg_mul_pow]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hκ0)) (pow_ne_zero _ hq)
    · refine (continuousAt_const.mul (by fun_prop)).mul
        (continuousAt_searsSum n hqn ?_ ?_ ?_ ?_ ?_ ?_ hD h₁ ?_)
      all_goals try fun_prop
      simp [qPochhammer_zero_param]
  by_cases hd : d = 0
  · -- the case `d = 0`, by continuity in `d`
    subst hd
    set L : ℂ → ℂ := fun t => qPochhammer e q n * phiSum q n b c t e (t * e * q ^ n / (b * c))
      with hL
    set R : ℂ → ℂ := fun t => qPochhammer (e / c) q n *
      searsSum q n c (t / b) 0 t (c * q * Q / e) 0 with hR
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L t = R t := by
      filter_upwards [self_mem_nhdsWithin, eventually_qPochhammer_mul_ne_zero one_ne_zero hq 0 n]
        with t ht0 hT
      rw [mul_one] at hT
      exact main t ht0 hT
    have key := eq_of_eventually_punctured (a := 0) ?_ ?_ hev
    · simpa [hL, hR] using key
    · exact continuousAt_const.mul (continuousAt_phiSum n hqn (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop) (by fun_prop) hD hE)
    · exact continuousAt_const.mul (continuousAt_searsSum n hqn (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) hD h₁ (by simp))
  · exact main d hd hD


/-- The terminating `₂φ₁` transformation
`(c;q)_n ₂φ₁(q⁻ⁿ,b;c;q,z) = (c/b;q)_n ₃φ₂(q⁻ⁿ,b,bzq⁻ⁿ/c;bq^{1-n}/c,0;q,q)`, cleared of
denominators, as the limit `B, D → 0` of DLMF 17.9.10 (DLMF 17.9.5). -/
theorem phiSum_two_one_sears {b c q : ℂ} (z : ℂ) (n : ℕ) (hq : q ≠ 0) (hqn : ‖q‖ < 1)
    (hb : b ≠ 0) (hc : c ≠ 0) (hC : qPochhammer c q n ≠ 0)
    (h₁ : qPochhammer (b * q * q⁻¹ ^ n / c) q n ≠ 0) :
    qPochhammer c q n * phiSum q n b 0 c 0 z =
      qPochhammer (c / b) q n *
        searsSum q n b (b * z * q⁻¹ ^ n / c) 0 (b * q * q⁻¹ ^ n / c) 0 0 := by
  have hqn0 : q ^ n * q⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hq, one_pow]
  set ρ := b * z * q⁻¹ ^ n / c with hρ
  set L : ℂ → ℂ := fun t => qPochhammer c q n * phiSum q n t b (t * ρ) c z with hL
  set R : ℂ → ℂ := fun t => qPochhammer (c / b) q n *
    searsSum q n b ρ 0 (t * ρ) (b * q * q⁻¹ ^ n / c) 0 with hR
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L t = R t := by
    filter_upwards [self_mem_nhdsWithin, eventually_qPochhammer_mul_ne_zero' ρ hq 0 n]
      with t ht0 hT
    have ht : t ≠ 0 := ht0
    have H := phiSum_three_two_third n hq hqn ht hb hc hT hC h₁
    rw [show t * ρ * c * q ^ n / (t * b) = z by
      rw [hρ]; field_simp; linear_combination z * hqn0,
      show t * ρ / t = ρ by field_simp] at H
    exact H
  have key := eq_of_eventually_punctured (a := 0) ?_ ?_ hev
  · simp only [hL, hR, zero_mul] at key
    have s1 : phiSum q n 0 b 0 c z = phiSum q n b 0 c 0 z := by
      unfold phiSum; exact sum_congr rfl fun k _ => by ring
    have s2 : searsSum q n b ρ 0 0 (b * q * q⁻¹ ^ n / c) 0 =
        searsSum q n b ρ 0 (b * q * q⁻¹ ^ n / c) 0 0 := by
      unfold searsSum; exact sum_congr rfl fun k _ => by ring
    rw [s1, s2] at key
    exact key
  · exact continuousAt_const.mul (continuousAt_phiSum n hqn (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop) (by fun_prop) (by simp [qPochhammer_zero_param]) hC)
  · exact continuousAt_const.mul (continuousAt_searsSum n hqn (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by simp [qPochhammer_zero_param])
      h₁ (by simp [qPochhammer_zero_param]))


/-- The terminating `₂φ₁` transformation
`(c;q)_n ₂φ₁(q⁻ⁿ,b;c;q,z) = bⁿ (c/b;q)_n ₃φ₁(q⁻ⁿ,b,q/z;bq^{1-n}/c;q,z/c)`, cleared of
denominators, as the limit `B, D → ∞` of DLMF 17.9.9 (DLMF 17.9.2). -/
theorem phiSum_two_one_three_one {b c q z : ℂ} (n : ℕ) (hq : q ≠ 0) (hqn : ‖q‖ < 1)
    (hb : b ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0) (hC : qPochhammer c q n ≠ 0)
    (h₁ : qPochhammer (b * q * q⁻¹ ^ n / c) q n ≠ 0) :
    qPochhammer c q n * phiSum q n b 0 c 0 z =
      b ^ n * qPochhammer (c / b) q n *
        ∑ k ∈ range (n + 1), qPochhammer (q⁻¹ ^ n) q k * qPochhammer b q k *
          qPochhammer (q / z) q k / (qPochhammer (b * q * q⁻¹ ^ n / c) q k * qPochhammer q q k) *
          ((z / c) ^ k / ((-1) ^ k * q ^ k.choose 2)) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, q⁻¹ ^ n = Q := ⟨_, rfl⟩
  rw [hQ] at h₁ ⊢
  have hqz : q / z ≠ 0 := div_ne_zero hq hz
  set γ : ℕ → ℂ := fun k => qPochhammer Q q k * qPochhammer b q k /
    (qPochhammer c q k * qPochhammer q q k) with hγ
  set δ : ℕ → ℂ := fun k => qPochhammer Q q k * qPochhammer b q k * qPochhammer (q / z) q k /
    (qPochhammer (b * q * Q / c) q k * qPochhammer q q k) with hδ
  set L : ℂ → ℂ := fun t => qPochhammer c q n * ∑ k ∈ range (n + 1), γ k *
    ((∏ j ∈ range k, (t - 1 * q ^ j)) / ∏ j ∈ range k, (t - q / z * q ^ j)) * q ^ k with hL
  set R : ℂ → ℂ := fun t => b ^ n * qPochhammer (c / b) q n * ∑ k ∈ range (n + 1), δ k *
    ((q / c) ^ k / ∏ j ∈ range k, (t - q / z * q ^ j)) with hR
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), L t = R t := by
    filter_upwards [self_mem_nhdsWithin, eventually_qPochhammer_div_ne_zero (q / z) q 0 n]
      with t ht0 hT
    have ht : t ≠ 0 := ht0
    rw [← hQ] at h₁
    have H := phiSum_three_two_second n hq hqn (one_div_ne_zero ht) hb hc hT hC h₁
    rw [hQ, show q / z / t / (1 / t) = q / z by field_simp] at H
    have hS : searsSum q n (1 / t) b 0 (q / z / t) c 0 = ∑ k ∈ range (n + 1), γ k *
        ((∏ j ∈ range k, (t - 1 * q ^ j)) / ∏ j ∈ range k, (t - q / z * q ^ j)) * q ^ k := by
      unfold searsSum
      refine sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have e1 := pow_mul_qPochhammer_div (e := 1) (q := q) ht k
      have e2 := pow_mul_qPochhammer_div (e := q / z) (q := q) ht k
      have hTk : qPochhammer (q / z / t) q k ≠ 0 := qPochhammer_ne_zero_of_le hT hkn
      have htk : t ^ k ≠ 0 := pow_ne_zero _ ht
      simp only [hγ, qPochhammer_zero_param]
      rw [← e1, ← e2, mul_div_mul_left _ _ htk]
      rw [← hQ]
      field_simp
    have hP : phiSum q n b (q / z) (q / z / t) (b * q * Q / c) (1 / t * q / c) =
        ∑ k ∈ range (n + 1), δ k * ((q / c) ^ k / ∏ j ∈ range k, (t - q / z * q ^ j)) := by
      unfold phiSum
      refine sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      have e2 := pow_mul_qPochhammer_div (e := q / z) (q := q) ht k
      have hTk : qPochhammer (q / z / t) q k ≠ 0 := qPochhammer_ne_zero_of_le hT hkn
      have htk : t ^ k ≠ 0 := pow_ne_zero _ ht
      simp only [hδ]
      rw [show (1 / t * q / c) ^ k = (q / c) ^ k / t ^ k by rw [← div_pow]; congr 1; field_simp]
      rw [← e2, ← hQ]
      field_simp
    rw [hS, hP] at H
    exact H
  have hW : ∀ k, (∏ j ∈ range k, ((0 : ℂ) - q / z * q ^ j)) ≠ 0 := fun k => by
    rw [prod_neg_mul_pow]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hqz)) (pow_ne_zero _ hq)
  have key := eq_of_eventually_punctured (a := 0) ?_ ?_ hev
  · simp only [hL, hR] at key
    have s1 : ∑ k ∈ range (n + 1), γ k * ((∏ j ∈ range k, ((0 : ℂ) - 1 * q ^ j)) /
        ∏ j ∈ range k, (0 - q / z * q ^ j)) * q ^ k = phiSum q n b 0 c 0 z := by
      unfold phiSum
      refine sum_congr rfl fun k _ => ?_
      simp only [hγ, prod_neg_mul_pow, qPochhammer_zero_param]
      rw [← hQ, mul_div_mul_right _ _ (pow_ne_zero _ hq), ← div_pow,
        show -1 / -(q / z) = z / q by field_simp, div_pow]
      field_simp
    have s2 : ∀ k, δ k * ((q / c) ^ k / ∏ j ∈ range k, ((0 : ℂ) - q / z * q ^ j)) =
        δ k * ((z / c) ^ k / ((-1) ^ k * q ^ k.choose 2)) := by
      intro k
      rw [prod_neg_mul_pow, show -(q / z) = (-1) * (q / z) by ring, mul_pow]
      field_simp
      rw [mul_assoc, ← mul_pow, show q / z * (z / c) = q / c by field_simp]
    rw [s1, sum_congr rfl fun k _ => s2 k] at key
    simp only [hδ] at key
    rw [← hQ] at key ⊢
    exact key
  · refine continuousAt_const.mul (tendsto_finsetSum _ fun k _ => ?_)
    have h1 : ContinuousAt (fun t : ℂ => ∏ j ∈ range k, (t - 1 * q ^ j)) 0 := by fun_prop
    have h2 : ContinuousAt (fun t : ℂ => ∏ j ∈ range k, (t - q / z * q ^ j)) 0 := by fun_prop
    exact (continuousAt_const.mul (h1.div h2 (hW k))).mul continuousAt_const
  · refine continuousAt_const.mul (tendsto_finsetSum _ fun k _ => ?_)
    have h2 : ContinuousAt (fun t : ℂ => ∏ j ∈ range k, (t - q / z * q ^ j)) 0 := by fun_prop
    exact continuousAt_const.mul (continuousAt_const.div h2 (hW k))


