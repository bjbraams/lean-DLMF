/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.UnitArgument

/-!
# Terminating `ₚFₚ₋₁(1)` series with cleared denominators

For a terminating series of length `n`, multiplying the `k`-th term by
`∏_y (y + k)_{n-k}` over the lower parameters `y` clears all denominators. The cleared sum
`genClearedFiniteHG` is a polynomial in the parameters; it equals `∏_y (y)_n` times the ordinary
finite series whenever every `(y)_n` is nonzero, and it keeps its meaning when a lower parameter
is a nonpositive integer. In the latter case it is the natural form of the finite sums with
reciprocal factorials `1/(k + c)!` (vanishing for `k + c < 0`), such as Racah's sums for the
Wigner symbols.

Transformations of terminating series extend to the cleared sums for all parameters, by
continuity from the generic parameters.

## Main definitions

* `genClearedFiniteHG`: the terminating unit-argument series with cleared denominators.

## Main results

* `genClearedFiniteHG_eq_mul`: the cleared series is `∏_y (y)_n` times
  `generalizedHypergeometricTruncated`.
* `generalizedHypergeometricTruncated_eq_of_neg_natCast_mem`: a finite series with upper parameter
  `-N` has at most `N + 1` nonzero terms.
* `genClearedFiniteHG_sheppard`: Sheppard's terminating `₃F₂(1)` transformation in cleared form,
  for all parameters.
* `genClearedFiniteHG_whipple`: Whipple's balanced `₄F₃` transformation (DLMF 16.4.14) in
  cleared form, for all parameters.
-/

@[expose] public noncomputable section

open Complex Finset

namespace DLMF.Hypergeometric

/-- The terminating unit-argument series of length `n` with cleared denominators,
`∑_{k ≤ n} (∏_x (x)_k / k!) ∏_y (y + k)_{n-k}`, `x` over the upper and `y` over the lower
parameters. -/
def genClearedFiniteHG (n : ℕ) (a b : Multiset ℂ) : ℂ :=
  ∑ k ∈ range (n + 1), pochhammerProduct a k / k.factorial *
      (b.map fun y => pochhammer (y + k) (n - k)).prod

/-- When no `(y)_n` vanishes, the cleared series is `∏_y (y)_n` times the finite series. -/
theorem genClearedFiniteHG_eq_mul {n : ℕ} (a b : Multiset ℂ) (hb : ∀ y ∈ b, pochhammer y n ≠ 0) :
    genClearedFiniteHG n a b = pochhammerProduct b n *
        generalizedHypergeometricTruncated n a b 1 := by
  unfold genClearedFiniteHG generalizedHypergeometricTruncated
  rw [mul_sum]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hsplit : pochhammerProduct b n = pochhammerProduct b k *
      (b.map fun y => pochhammer (y + k) (n - k)).prod := by
    unfold pochhammerProduct
    rw [← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl fun y _ => ?_
    rw [← pochhammer_add, Nat.add_sub_cancel' hk']
  have hbk : pochhammerProduct b k ≠ 0 := by
    unfold pochhammerProduct
    refine Multiset.prod_ne_zero fun h0 => ?_
    obtain ⟨y, hy, hy0⟩ := Multiset.mem_map.mp h0
    exact pochhammer_ne_zero_of_le hk' (hb y hy) hy0
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [hsplit, generalizedHypergeometricCoeff, one_pow, mul_one]
  field_simp

/-- `(-N)ₖ ≠ 0` for `k ≤ N`. -/
theorem pochhammer_neg_natCast_ne_zero {N k : ℕ} (hk : k ≤ N) : pochhammer (-(N : ℂ)) k ≠ 0 := by
  rw [pochhammer_neg_coe_nat]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num))
    (by exact_mod_cast (Nat.descFactorial_pos.mpr hk).ne')

/-- A finite series with the upper parameter `-N` does not change when it is continued beyond
`N` terms. -/
theorem generalizedHypergeometricTruncated_eq_of_neg_natCast_mem {a : Multiset ℂ} (b : Multiset ℂ)
    (z : ℂ) {N m : ℕ}
    (hN : -(N : ℂ) ∈ a) (hm : N ≤ m) : generalizedHypergeometricTruncated m a b z =
        generalizedHypergeometricTruncated N a b z := by
  unfold generalizedHypergeometricTruncated
  refine (Finset.sum_subset (range_subset_range.2 (by omega)) fun k _ hk => ?_).symm
  have hk' : N < k := by simp only [mem_range, not_lt] at hk; omega
  have h0 : pochhammerProduct a k = 0 :=
    Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, hN, pochhammer_neg_nat_eq_zero hk'⟩)
  rw [generalizedHypergeometricCoeff, h0, zero_div, zero_mul]

/-- Two continuous functions on `ℂ` that agree off finitely many cosets `z + ℤ` agree. -/
private lemma eq_of_eq_off_intShifts {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (c : List ℂ) (h : ∀ t, (∀ z ∈ c, ∀ k : ℤ, t ≠ z + k) → f t = g t) : f = g := by
  set B : Set ℂ := ⋃ z ∈ {z | z ∈ c}, Set.range fun k : ℤ => z + k
  have hB : B.Countable :=
    (List.finite_toSet c).countable.biUnion fun z _ => Set.countable_range _
  refine hf.ext_on (hB.dense_compl ℂ) hg fun t ht => h t fun z hz k hk => ht ?_
  exact Set.mem_biUnion hz ⟨k, hk.symm⟩

/-- A parameter avoiding the cosets `-ℕ`. -/
private lemma ne_neg_nat_of_off {t z w : ℂ} (h : ∀ k : ℤ, t ≠ z + k) (hw : w = t - z) :
    ∀ k : ℕ, w ≠ -k := by
  intro k hk
  exact h (-k) (by rw [hw] at hk; push_cast; linear_combination hk)

/-- A parameter avoiding the cosets `-ℕ`, reflected. -/
private lemma ne_neg_nat_of_off' {t z w : ℂ} (h : ∀ k : ℤ, t ≠ z + k) (hw : w = z - t) :
    ∀ k : ℕ, w ≠ -k := by
  intro k hk
  exact h k (by rw [hw] at hk; push_cast; linear_combination -hk)

/-- The cleared series of three over two parameters, written out. -/
private lemma genClearedFiniteHG_three_two (n : ℕ) (a₁ a₂ a₃ b₁ b₂ : ℂ) :
    genClearedFiniteHG n {a₁, a₂, a₃} {b₁, b₂} =
      ∑ k ∈ range (n + 1), pochhammer a₁ k * pochhammer a₂ k * pochhammer a₃ k / k.factorial *
        (pochhammer (b₁ + k) (n - k) * pochhammer (b₂ + k) (n - k)) := by
  simp only [genClearedFiniteHG, pochhammerProduct, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, mul_assoc]

/-- The cleared series of four over three parameters, written out. -/
private lemma genClearedFiniteHG_four_three (n : ℕ) (a₁ a₂ a₃ a₄ b₁ b₂ b₃ : ℂ) :
    genClearedFiniteHG n {a₁, a₂, a₃, a₄} {b₁, b₂, b₃} =
      ∑ k ∈ range (n + 1), pochhammer a₁ k * pochhammer a₂ k * pochhammer a₃ k *
          pochhammer a₄ k / k.factorial *
        (pochhammer (b₁ + k) (n - k) * pochhammer (b₂ + k) (n - k) *
            pochhammer (b₃ + k) (n - k)) := by
  simp only [genClearedFiniteHG, pochhammerProduct, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, mul_assoc]

/-- Continuity of a Pochhammer symbol in an affine parameter. -/
private lemma continuous_pochhammer_affine (u v : ℂ) (k : ℕ) :
    Continuous fun t : ℂ => pochhammer (u + v * t) k :=
  (ascPochhammer ℂ k).continuous.comp (by fun_prop)

/-- Sheppard's transformation of a terminating `₃F₂(1)` in cleared form, for all parameters:
`∑ₖ (-n)ₖ(Q)ₖ(P)ₖ/k! (R+k)_{n-k}(D+k)_{n-k}`
`= (-1)ⁿ ∑ₖ (-n)ₖ(P)ₖ(R-Q)ₖ/k! (R+k)_{n-k}(1+P-D-n+k)_{n-k}`. -/
theorem genClearedFiniteHG_sheppard (n : ℕ) (P Q R D : ℂ) :
    genClearedFiniteHG n {(-n : ℂ), Q, P} {R, D} =
      (-1) ^ n * genClearedFiniteHG n {(-n : ℂ), P, R - Q} {R, 1 + P - D - n} := by
  have key := eq_of_eq_off_intShifts (c := [-R, -D, 1 - D + P - n])
    (f := fun t => genClearedFiniteHG n {(-n : ℂ), Q, P} {R + t, D + t})
    (g := fun t => (-1) ^ n * genClearedFiniteHG n {(-n : ℂ), P, R + t - Q}
      {R + t, 1 + P - (D + t) - n}) ?_ ?_ ?_
  · simpa using congrFun key 0
  · simp only [genClearedFiniteHG_three_two]
    refine continuous_finsetSum _ fun k _ => ?_
    exact (continuous_const
        (y := pochhammer (-(n : ℂ)) k * pochhammer Q k * pochhammer P k / k.factorial)).mul
      ((continuous_pochhammer_affine (R + k) 1 (n - k)).mul
          (continuous_pochhammer_affine (D + k) 1 (n - k)))
      |>.congr fun t => by simp only [Pi.mul_apply]; ring_nf
  · simp only [genClearedFiniteHG_three_two]
    refine continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)
    exact ((continuous_const (y := pochhammer (-(n : ℂ)) k * pochhammer P k / k.factorial)).mul
      (continuous_pochhammer_affine (R - Q) 1 k)).mul
      ((continuous_pochhammer_affine (R + k) 1 (n - k)).mul
        (continuous_pochhammer_affine (1 + P - D - n + k) (-1) (n - k)))
      |>.congr fun t => by simp only [Pi.mul_apply]; ring_nf
  · intro t ht
    have hR : ∀ k : ℕ, R + t ≠ -k :=
      ne_neg_nat_of_off (ht (-R) (by simp)) (by ring)
    have hD : ∀ k : ℕ, D + t ≠ -k :=
      ne_neg_nat_of_off (ht (-D) (by simp)) (by ring)
    have hE : ∀ k : ℕ, 1 + P - (D + t) - n ≠ -k :=
      ne_neg_nat_of_off' (ht (1 - D + P - n) (by simp)) (by ring)
    have hsh := generalizedHypergeometricTruncated_sheppard n P Q (R + t) (D + t) hR
      (pochhammer_ne_zero_of_not_neg_nat hD n)
      (by convert pochhammer_ne_zero_of_not_neg_nat hE n using 2; ring)
    have hrefl : pochhammer (1 + P - (D + t) - n) n = (-1) ^ n * pochhammer (D + t - P) n := by
      rw [← pochhammer_reflect]; congr 1; ring
    rw [genClearedFiniteHG_eq_mul _ _ (by
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
        rintro y (rfl | rfl)
        · exact pochhammer_ne_zero_of_not_neg_nat hR n
        · exact pochhammer_ne_zero_of_not_neg_nat hD n),
      genClearedFiniteHG_eq_mul _ _ (by
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
        rintro y (rfl | rfl)
        · exact pochhammer_ne_zero_of_not_neg_nat hR n
        · exact pochhammer_ne_zero_of_not_neg_nat hE n)]
    simp only [pochhammerProduct, Multiset.insert_eq_cons, Multiset.map_cons,
        Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
    rw [hrefl]
    have hs : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    linear_combination pochhammer (R + t) n * hsh - pochhammer (R + t) n *
      pochhammer (D + t - P) n * generalizedHypergeometricTruncated n {(-n : ℂ), P, R + t - Q}
        {R + t, 1 + P - (D + t) - n} 1 * hs

/-- Whipple's balanced terminating `₄F₃(1)` transformation (DLMF 16.4.14) in cleared form, for
all parameters with `a + b + c - n + 1 = d + e + f`. -/
theorem genClearedFiniteHG_whipple (n : ℕ) (a b c d e f : ℂ)
    (hbal : a + b + c - n + 1 = d + e + f) :
    genClearedFiniteHG n {(-n : ℂ), a, b, c} {d, e, f} =
      genClearedFiniteHG n {(-n : ℂ), a, d - b, d - c} {d, a - e - n + 1, a - f - n + 1} := by
  have key := eq_of_eq_off_intShifts (c := [-d, -e, -f, a - e - n + 1, a - f - n + 1])
    (f := fun t => genClearedFiniteHG n {(-n : ℂ), a, b + 3 * t, c} {d + t, e + t, f + t})
    (g := fun t => genClearedFiniteHG n {(-n : ℂ), a, d + t - (b + 3 * t), d + t - c}
      {d + t, a - (e + t) - n + 1, a - (f + t) - n + 1}) ?_ ?_ ?_
  · simpa using congrFun key 0
  · simp only [genClearedFiniteHG_four_three]
    refine continuous_finsetSum _ fun k _ => ?_
    exact (((continuous_const (y := pochhammer (-(n : ℂ)) k * pochhammer a k)).mul
      (continuous_pochhammer_affine b 3 k)).mul
          (continuous_const (y := pochhammer c k / k.factorial))).mul
      (((continuous_pochhammer_affine (d + k) 1 (n - k)).mul
        (continuous_pochhammer_affine (e + k) 1 (n - k))).mul
        (continuous_pochhammer_affine (f + k) 1 (n - k)))
      |>.congr fun t => by simp only [Pi.mul_apply]; ring_nf
  · simp only [genClearedFiniteHG_four_three]
    refine continuous_finsetSum _ fun k _ => ?_
    exact (((continuous_const (y := pochhammer (-(n : ℂ)) k * pochhammer a k)).mul
      (continuous_pochhammer_affine (d - b) (-2) k)).mul
      ((continuous_pochhammer_affine (d - c) 1 k).div_const (k.factorial : ℂ))).mul
      (((continuous_pochhammer_affine (d + k) 1 (n - k)).mul
        (continuous_pochhammer_affine (a - e - n + 1 + k) (-1) (n - k))).mul
        (continuous_pochhammer_affine (a - f - n + 1 + k) (-1) (n - k)))
      |>.congr fun t => by simp only [Pi.mul_apply]; ring_nf
  · intro t ht
    have hd : ∀ k : ℕ, d + t ≠ -k := ne_neg_nat_of_off (ht (-d) (by simp)) (by ring)
    have he : ∀ k : ℕ, e + t ≠ -k := ne_neg_nat_of_off (ht (-e) (by simp)) (by ring)
    have hf : ∀ k : ℕ, f + t ≠ -k := ne_neg_nat_of_off (ht (-f) (by simp)) (by ring)
    have he' : ∀ k : ℕ, a - (e + t) - n + 1 ≠ -k :=
      ne_neg_nat_of_off' (ht (a - e - n + 1) (by simp)) (by ring)
    have hf' : ∀ k : ℕ, a - (f + t) - n + 1 ≠ -k :=
      ne_neg_nat_of_off' (ht (a - f - n + 1) (by simp)) (by ring)
    have hw := generalizedHypergeometric_balanced_4F3_transformation n a (b + 3 * t) c (d + t)
        (e + t) (f + t)
      (by linear_combination hbal) (by
        simp only [LowerParametersRegular, Multiset.insert_eq_cons, Multiset.mem_cons,
          Multiset.mem_singleton]
        rintro y (rfl | rfl | rfl | rfl | rfl)
        exacts [hd, he, hf, he', hf'])
    have hpe := pochhammer_ne_zero_of_not_neg_nat he n
    have hpf := pochhammer_ne_zero_of_not_neg_nat hf n
    have hre : pochhammer (a - (e + t) - n + 1) n = (-1) ^ n * pochhammer (e + t - a) n := by
      rw [← pochhammer_reflect]; congr 1; ring
    have hrf : pochhammer (a - (f + t) - n + 1) n = (-1) ^ n * pochhammer (f + t - a) n := by
      rw [← pochhammer_reflect]; congr 1; ring
    rw [genClearedFiniteHG_eq_mul _ _ (by
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
        rintro y (rfl | rfl | rfl)
        exacts [pochhammer_ne_zero_of_not_neg_nat hd n, hpe, hpf]),
      genClearedFiniteHG_eq_mul _ _ (by
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
        rintro y (rfl | rfl | rfl)
        exacts [pochhammer_ne_zero_of_not_neg_nat hd n, pochhammer_ne_zero_of_not_neg_nat he' n,
          pochhammer_ne_zero_of_not_neg_nat hf' n])]
    simp only [pochhammerProduct, Multiset.insert_eq_cons, Multiset.map_cons,
        Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
    simp only [Multiset.insert_eq_cons] at hw
    rw [hw, hre, hrf]
    have hs : ((-1 : ℂ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    field_simp
    linear_combination (norm := ring_nf) -(pochhammer (d + t) n * pochhammer (e + t - a) n *
      pochhammer (f + t - a) n *
          generalizedHypergeometricTruncated n
          ((-n : ℂ) ::ₘ a ::ₘ (d + t - (b + 3 * t)) ::ₘ {d + t - c})
        ((d + t) ::ₘ (a - (e + t) - n + 1) ::ₘ {a - (f + t) - n + 1}) 1) * hs

end DLMF.Hypergeometric
