/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bailey
public import DLMF.QHypergeometric.Transformations

/-!
# Finite bilateral transformations

An upper parameter `q⁻ᴺ` and a lower parameter `qᴹ⁺¹` restrict a bilateral basic
hypergeometric series to the integer interval `[-M,N]`. The finite form retains the
zero values of totalized negative shifted factorials at exceptional lower parameters.
-/

@[expose] public noncomputable section

open Complex Finset Filter
open scoped Topology
open DLMF.QSeries

namespace DLMF.QHypergeometric.FiniteBilateral

/-- A positive-power lower parameter annihilates the terms below the finite left endpoint.
-/
lemma qPochhammerInt_pow_eq_zero {q : ℂ} (hq0 : q ≠ 0) (M j : ℕ) (hj : M ≤ j) :
    qPochhammerInt (q ^ (M + 1)) q (Int.negSucc j) = 0 := by
  rw [qPochhammerInt_negSucc]
  have he : q ^ (M + 1) * q ^ (-((j : ℤ) + 1)) = q ^ (-((j - M : ℕ) : ℤ)) := by
    rw [← zpow_natCast q (M + 1), ← zpow_add₀ hq0]
    congr 1
    rw [Nat.cast_sub hj]
    push_cast
    ring
  rw [he]
  have hz : qPochhammer (q ^ (-((j - M : ℕ) : ℤ))) q (j + 1) = 0 := by
    simpa only [zpow_neg, zpow_natCast] using
      qPochhammer_recip_pow_eq_zero hq0 (by omega : j - M < j + 1)
  rw [hz, inv_zero]

/-- An upper terminating parameter annihilates all terms above the finite right endpoint. -/
lemma qPsiTerm_eq_zero_of_lt {q z : ℂ} (hq0 : q ≠ 0) (N : ℕ)
    (a b : List ℂ) (k : ℤ) (hk : (N : ℤ) < k) :
    qPsiTerm (q ^ (-(N : ℤ)) :: a) b q z k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j := ⟨k.toNat, by omega⟩
  have hNj : N < j := by omega
  have hz : qPochhammer (q ^ (-(N : ℤ))) q j = 0 := by
    simpa only [zpow_neg, zpow_natCast] using qPochhammer_recip_pow_eq_zero hq0 hNj
  simp only [qPsiTerm, qPochhammerListInt, List.map_cons, List.prod_cons,
    qPochhammerInt_natCast, hz, zero_mul, zero_div]

/-- A lower positive-power parameter annihilates terms below the finite left endpoint. -/
lemma qPsiTerm_eq_zero_of_lt_neg {q z : ℂ} (hq0 : q ≠ 0) (M : ℕ)
    (a b : List ℂ) (k : ℤ) (hk : k < -(M : ℤ)) :
    qPsiTerm a (q ^ (M + 1) :: b) q z k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = Int.negSucc j :=
    ⟨(-k - 1).toNat, by omega⟩
  have hMj : M ≤ j := by omega
  simp only [qPsiTerm, qPochhammerListInt, List.map_cons, List.prod_cons,
    qPochhammerInt_pow_eq_zero hq0 M j hMj, zero_mul, div_zero]

/-- A doubly terminating bilateral series is a finite integer-interval sum. -/
lemma qPsi_eq_sum_Icc {q z : ℂ} (hq0 : q ≠ 0) (M N : ℕ) (a b : List ℂ) :
    qPsi (q ^ (-(N : ℤ)) :: a) (q ^ (M + 1) :: b) q z =
      ∑ k ∈ Icc (-(M : ℤ)) (N : ℤ),
        qPsiTerm (q ^ (-(N : ℤ)) :: a) (q ^ (M + 1) :: b) q z k := by
  unfold qPsi
  apply tsum_eq_sum
  intro k hk
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  rcases hk with hk | hk
  · exact qPsiTerm_eq_zero_of_lt_neg hq0 M _ _ k hk
  · exact qPsiTerm_eq_zero_of_lt hq0 N _ _ k hk

/-- Shifting a list of integer-index products to a natural index factors out its base value.
-/
lemma qPochhammerListInt_sub {q : ℂ} (hq0 : q ≠ 0) (a : List ℂ) (M k : ℕ)
    (ha : ∀ x ∈ a, qPochhammer (x / q ^ M) q M ≠ 0) :
    qPochhammerListInt a q ((k : ℤ) - M) =
      qPochhammerList (a.map fun x => x / q ^ M) q k /
        qPochhammerList (a.map fun x => x / q ^ M) q M := by
  induction a with
  | nil => simp [qPochhammerListInt, qPochhammerList]
  | cons x a ih =>
    have hx := ha x (by simp)
    have ht : ∀ y ∈ a, qPochhammer (y / q ^ M) q M ≠ 0 := fun y hy =>
      ha y (by simp [hy])
    simp only [qPochhammerListInt, List.map_cons, List.prod_cons] at ih ⊢
    rw [RamanujanPsi.qPochhammerInt_natCast_sub hq0 M k hx, ih ht]
    simp only [qPochhammerList, List.map_cons, List.prod_cons]
    ring

/-- A finite bilateral interval can be enumerated by natural indices after a shift. -/
lemma sum_Icc_eq_sum_range (f : ℤ → ℂ) (M N : ℕ) :
    (∑ k ∈ Icc (-(M : ℤ)) (N : ℤ), f k) =
      ∑ j ∈ range (M + N + 1), f ((j : ℤ) - M) := by
  symm
  apply sum_bij (fun (j : ℕ) _ => (j : ℤ) - M)
  · intro j hj
    have := Finset.mem_range.mp hj
    simp only [Finset.mem_Icc]
    omega
  · intro j hj k hk he
    omega
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    refine ⟨(k + M).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro j hj
    rfl

/-- A shifted bilateral term becomes a unilateral term when the forced lower parameter is
`q^(M+1)` and the shifted finite denominator products are nonzero. -/
lemma qPsiTerm_shift {q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hz0 : z ≠ 0)
    (a b : List ℂ) (M k : ℕ) (hlen : a.length = b.length + 1)
    (ha : ∀ x ∈ a, qPochhammer (x / q ^ M) q M ≠ 0)
    (hb : ∀ x ∈ b, qPochhammer (x / q ^ M) q M ≠ 0) :
    qPsiTerm a (q ^ (M + 1) :: b) q z ((k : ℤ) - M) =
      (qPochhammer q q M * qPochhammerList (b.map fun x => x / q ^ M) q M /
        qPochhammerList (a.map fun x => x / q ^ M) q M * z ^ (-(M : ℤ))) *
        qPhiTerm (a.map fun x => x / q ^ M) (b.map fun x => x / q ^ M) q z k := by
  have hshift : q ^ (M + 1) / q ^ M = q := by rw [pow_succ]; field_simp
  have hlow : ∀ x ∈ q ^ (M + 1) :: b, qPochhammer (x / q ^ M) q M ≠ 0 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hshift]
      exact qPochhammer_self_ne_zero hq M
    · exact hb x hx
  have he : qPsiExponent a (q ^ (M + 1) :: b) = 0 := by
    simp [qPsiExponent, hlen]
  have he' : qPhiExponent (a.map fun x => x / q ^ M) (b.map fun x => x / q ^ M) = 0 := by
    simp only [qPhiExponent, List.length_map, hlen, Nat.cast_add, Nat.cast_one]
    omega
  rw [qPsiTerm, he, zpow_zero, mul_one,
    qPochhammerListInt_sub hq0 a M k ha,
    qPochhammerListInt_sub hq0 _ M k hlow]
  simp only [List.map_cons, qPochhammerList, List.map_cons, List.prod_cons, hshift]
  rw [qPhiTerm, he', zpow_zero, mul_one, zpow_sub₀ hz0, zpow_natCast, zpow_natCast,
    zpow_neg, zpow_natCast]
  have hnonzero (l : List ℂ)
      (hl : ∀ x ∈ l, qPochhammer (x / q ^ M) q M ≠ 0) :
      qPochhammerList (l.map fun x => x / q ^ M) q M ≠ 0 := by
    apply List.prod_ne_zero
    simp only [List.mem_map, not_exists, not_and]
    intro x hx he
    rcases hx with ⟨y, hy, rfl⟩
    exact hl y hy he
  have hAM := hnonzero a ha
  have hBM := hnonzero b hb
  simp only [qPochhammerList] at hAM hBM ⊢
  field_simp [hAM, hBM, qPochhammer_self_ne_zero hq M]

/-- A regular finite bilateral series is a terminating unilateral series after shifting the
left endpoint to zero. -/
lemma qPsi_eq_qPhi_shift {q z : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hz0 : z ≠ 0)
    (a b : List ℂ) (M N : ℕ) (hlen : a.length = b.length)
    (ha : ∀ x ∈ q ^ (-(N : ℤ)) :: a, qPochhammer (x / q ^ M) q M ≠ 0)
    (hb : ∀ x ∈ b, qPochhammer (x / q ^ M) q M ≠ 0) :
    qPsi (q ^ (-(N : ℤ)) :: a) (q ^ (M + 1) :: b) q z =
      (qPochhammer q q M * qPochhammerList (b.map fun x => x / q ^ M) q M /
        qPochhammerList ((q ^ (-(N : ℤ)) :: a).map fun x => x / q ^ M) q M *
        z ^ (-(M : ℤ))) *
        qPhi ((q ^ (-(N : ℤ)) :: a).map fun x => x / q ^ M)
          (b.map fun x => x / q ^ M) q z := by
  have he : q ^ (-(N : ℤ)) / q ^ M = q ^ (-((M + N : ℕ) : ℤ)) := by
    rw [← zpow_natCast q M, ← zpow_sub₀ hq0]
    congr 1
    push_cast
    ring
  have ht : qPhi ((q ^ (-(N : ℤ)) :: a).map fun x => x / q ^ M)
      (b.map fun x => x / q ^ M) q z =
      ∑ k ∈ range (M + N + 1),
        qPhiTerm ((q ^ (-(N : ℤ)) :: a).map fun x => x / q ^ M)
          (b.map fun x => x / q ^ M) q z k := by
    simp only [List.map_cons, he]
    exact qPhi_terminates hq0 (M + N)
  rw [qPsi_eq_sum_Icc hq0 M N a b, sum_Icc_eq_sum_range, ht, mul_sum]
  apply sum_congr rfl
  intro k hk
  exact qPsiTerm_shift hq0 hq hz0 _ b M k (by simp [hlen]) ha hb

/-- Permuting upper or lower parameters preserves a bilateral term. -/
lemma qPsiTerm_perm {a a' b b' : List ℂ} (ha : a.Perm a') (hb : b.Perm b')
    (q z : ℂ) (k : ℤ) : qPsiTerm a b q z k = qPsiTerm a' b' q z k := by
  have hA := (ha.map fun x => qPochhammerInt x q k).prod_eq
  have hB := (hb.map fun x => qPochhammerInt x q k).prod_eq
  simp only [qPsiTerm, qPochhammerListInt, hA, hB, qPsiExponent, ha.length_eq, hb.length_eq]

/-- Permuting upper or lower parameters preserves a bilateral series. -/
lemma qPsi_perm {a a' b b' : List ℂ} (ha : a.Perm a') (hb : b.Perm b')
    (q z : ℂ) : qPsi a b q z = qPsi a' b' q z :=
  tsum_congr fun k => qPsiTerm_perm ha hb q z k

/-- The negative-index prefix of an upper parameter is nonzero when the positive q-lattice
is excluded; the parameter itself may be zero. -/
lemma qPochhammer_div_pow_ne_zero {x q : ℂ} (hq0 : q ≠ 0)
    (hx : ∀ j : ℕ, x ≠ q ^ (j + 1)) (M : ℕ) :
    qPochhammer (x / q ^ M) q M ≠ 0 := by
  rw [qPochhammer_eq_prod]
  apply prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro he
  have hjM : j < M := Finset.mem_range.mp hj
  have he' : x * q ^ j = q ^ M := by
    have : x / q ^ M * q ^ j = 1 := he.symm
    field_simp at this
    exact this
  apply hx (M - j - 1)
  apply mul_right_cancel₀ (pow_ne_zero j hq0)
  rw [he', show M - j - 1 + 1 = M - j by omega, ← pow_add,
    Nat.sub_add_cancel (by omega : j ≤ M)]

/-- A negative-index bilateral term is a quotient of ordinary finite products. -/
lemma qPsiTerm_negSucc (a b : List ℂ) (q z : ℂ) (j : ℕ) :
    qPsiTerm a b q z (Int.negSucc j) =
      qPochhammerList (b.map fun x => x * q ^ (-((j : ℤ) + 1))) q (j + 1) /
        qPochhammerList (a.map fun x => x * q ^ (-((j : ℤ) + 1))) q (j + 1) *
      (((-1 : ℂ) ^ (Int.negSucc j) * q ^ TripleProduct.tri (Int.negSucc j)) ^
        qPsiExponent a b) * z ^ (Int.negSucc j) := by
  have hp (l : List ℂ) : qPochhammerListInt l q (Int.negSucc j) =
      (qPochhammerList (l.map fun x => x * q ^ (-((j : ℤ) + 1))) q (j + 1))⁻¹ := by
    induction l with
    | nil => simp [qPochhammerListInt, qPochhammerList]
    | cons x l ih =>
      simp only [qPochhammerListInt, qPochhammerList, List.map_cons, List.prod_cons,
        qPochhammerInt_negSucc, mul_inv] at ih ⊢
      rw [ih]
  rw [qPsiTerm, hp, hp, inv_div_inv]

/-- Finite shifted factorials vary continuously with their upper parameter. -/
lemma continuousAt_qPochhammer {f : ℂ → ℂ} {x : ℂ} (hf : ContinuousAt f x)
    (q : ℂ) (n : ℕ) : ContinuousAt (fun y => qPochhammer (f y) q n) x := by
  exact (continuous_qPochhammer q n).continuousAt.comp hf

/-- A finite product of parameterized shifted factorials is continuous wherever each
parameter is continuous. -/
lemma continuousAt_qPochhammerList {l : List (ℂ → ℂ)} {x : ℂ}
    (hl : ∀ f ∈ l, ContinuousAt f x) (q : ℂ) (n : ℕ) :
    ContinuousAt (fun y => qPochhammerList (l.map fun f => f y) q n) x := by
  induction l with
  | nil => simpa only [qPochhammerList, List.map_nil, List.prod_nil] using continuousAt_const
  | cons f l ih =>
    simp only [qPochhammerList, List.map_cons, List.prod_cons] at ih ⊢
    exact (continuousAt_qPochhammer (hl f (by simp)) q n).mul
      (ih fun g hg => hl g (by simp [hg]))

/-- A bilateral term is continuous in its parameters away from its natural lower and
negative-index upper poles. -/
lemma continuousAt_qPsiTerm {a b : List (ℂ → ℂ)} {z : ℂ → ℂ} {x : ℂ}
    {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : ∀ f ∈ a, ContinuousAt f x) (hb : ∀ f ∈ b, ContinuousAt f x)
    (hz : ContinuousAt z x) (hz0 : z x ≠ 0)
    (hreg : QBilateralRegular (a.map fun f => f x) (b.map fun f => f x) q) (k : ℤ) :
    ContinuousAt (fun y => qPsiTerm (a.map fun f => f y) (b.map fun f => f y) q (z y) k) x := by
  have hnonzero (l : List ℂ) (n : ℕ) (hl : ∀ u ∈ l, qPochhammer u q n ≠ 0) :
      qPochhammerList l q n ≠ 0 := by
    apply List.prod_ne_zero
    simp only [List.mem_map, not_exists, not_and]
    intro u hu he
    exact hl u hu he
  cases k with
  | ofNat n =>
    have hd : qPochhammerList (b.map fun f => f x) q n ≠ 0 :=
      hnonzero _ n fun u hu => qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hreg.1 hu n
    simp only [Int.ofNat_eq_natCast, qPsiTerm, qPochhammerListInt_natCast,
      qPsiExponent, List.length_map]
    exact (((continuousAt_qPochhammerList ha q n).div
      (continuousAt_qPochhammerList hb q n) hd).mul continuousAt_const).mul
      (by simpa only [zpow_natCast] using hz.fun_pow n)
  | negSucc n =>
    have hp (l : List (ℂ → ℂ)) (hl : ∀ f ∈ l, ContinuousAt f x) :
        ContinuousAt (fun y => qPochhammerList
          ((l.map fun f => f y).map fun u => u * q ^ (-((n : ℤ) + 1))) q (n + 1)) x := by
      have hc : ∀ f ∈ l.map (fun f => fun y => f y * q ^ (-((n : ℤ) + 1))),
          ContinuousAt f x := by
        intro f hf
        rcases List.mem_map.mp hf with ⟨g, hg, rfl⟩
        exact (hl g hg).mul continuousAt_const
      simpa only [List.map_map, Function.comp_def] using
        continuousAt_qPochhammerList hc q (n + 1)
    have hd : qPochhammerList ((a.map fun f => f x).map
        fun u => u * q ^ (-((n : ℤ) + 1))) q (n + 1) ≠ 0 := by
      apply hnonzero
      intro u hu
      rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
      rw [show v * q ^ (-((n : ℤ) + 1)) = v / q ^ (n + 1) by
        rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; rfl,
          zpow_neg, zpow_natCast, div_eq_mul_inv]]
      exact qPochhammer_div_pow_ne_zero hq0 (hreg.2 v hv) (n + 1)
    simp only [qPsiTerm_negSucc, qPsiExponent, List.length_map]
    exact (((hp b hb).div (hp a ha) hd).mul continuousAt_const).mul (hz.zpow₀ _ (Or.inl hz0))

/-- A finite bilateral series varies continuously with its parameters on its regular domain.
-/
lemma continuousAt_qPsi_finite {a b : List (ℂ → ℂ)} {z : ℂ → ℂ} {x : ℂ}
    {q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (ha : ∀ f ∈ a, ContinuousAt f x) (hb : ∀ f ∈ b, ContinuousAt f x)
    (hz : ContinuousAt z x) (hz0 : z x ≠ 0) (M N : ℕ)
    (hreg : QBilateralRegular (q ^ (-(N : ℤ)) :: a.map fun f => f x)
      (q ^ (M + 1) :: b.map fun f => f x) q) :
    ContinuousAt (fun y => qPsi (q ^ (-(N : ℤ)) :: a.map fun f => f y)
      (q ^ (M + 1) :: b.map fun f => f y) q (z y)) x := by
  simp_rw [qPsi_eq_sum_Icc hq0 M N]
  change Tendsto _ (𝓝 x) (𝓝 _)
  apply tendsto_finsetSum
  intro k hk
  have hA : ∀ f ∈ (fun _ : ℂ => q ^ (-(N : ℤ))) :: a, ContinuousAt f x := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact continuousAt_const
    · exact ha f hf
  have hB : ∀ f ∈ (fun _ : ℂ => q ^ (M + 1)) :: b, ContinuousAt f x := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact continuousAt_const
    · exact hb f hf
  simpa only [List.map_cons] using (continuousAt_qPsiTerm hq0 hq hA hB hz hz0 hreg k).tendsto

/-- A monomial upper parameter has no finite shifted-factorial zeros near a point except
possibly at the point itself. -/
lemma eventually_qPochhammer_mul_pow_ne_zero (u q r₀ : ℂ) (m N : ℕ) (hm : 0 < m) :
    ∀ᶠ r in 𝓝[≠] r₀, qPochhammer (u * r ^ m) q N ≠ 0 := by
  have H : ∀ᶠ r in 𝓝[≠] r₀, ∀ j ∈ range N, 1 - u * r ^ m * q ^ j ≠ 0 := by
    rw [eventually_all_finset]
    intro j hj
    let P : Polynomial ℂ := 1 - Polynomial.C (u * q ^ j) * Polynomial.X ^ m
    have hp : P ≠ 0 := by
      intro he
      have h := congrArg (fun p : Polynomial ℂ => p.eval 0) he
      simp [P, Nat.ne_of_gt hm] at h
    have h := (Polynomial.eventually_eval_ne_zero_cofinite hp).filter_mono
      (nhdsNE_le_cofinite r₀)
    simpa only [P, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_assoc,
      mul_left_comm, mul_comm] using h
  filter_upwards [H] with r hr
  rw [qPochhammer_eq_prod]
  exact prod_ne_zero_iff.mpr hr

/-- A reciprocal monomial upper parameter has no finite shifted-factorial zeros near a point
except possibly at that point. -/
lemma eventually_qPochhammer_div_pow_ne_zero {u q : ℂ} (hu0 : u ≠ 0) (hq0 : q ≠ 0)
    (r₀ : ℂ) (m N : ℕ) (hm : 0 < m) :
    ∀ᶠ r in 𝓝[≠] r₀, qPochhammer (u / r ^ m) q N ≠ 0 := by
  have hr0 : ∀ᶠ r in 𝓝[≠] r₀, r ≠ 0 :=
    le_cofinite_iff_eventually_ne.mp (nhdsNE_le_cofinite r₀) 0
  filter_upwards [hr0, eventually_qPochhammer_mul_pow_ne_zero
    (q ^ (1 - (N : ℤ)) / u) q r₀ m N hm] with r hr hp
  have hz : u / r ^ m ≠ 0 := div_ne_zero hu0 (pow_ne_zero _ hr)
  rw [qPochhammer_reverse hz hq0,
    show q ^ (1 - (N : ℤ)) / (u / r ^ m) = (q ^ (1 - (N : ℤ)) / u) * r ^ m by field_simp]
  exact mul_ne_zero (mul_ne_zero hp (pow_ne_zero _ (neg_ne_zero.mpr hz)))
    (pow_ne_zero _ hq0)

/-- The lower natural-index products and upper negative-index prefixes are regular on the
finite bilateral interval `[-N,N]`. -/
def RegularThrough (a b : List ℂ) (q : ℂ) (N : ℕ) : Prop :=
  (∀ x ∈ b, qPochhammer x q N ≠ 0) ∧
    (∀ x ∈ a, qPochhammer (x / q ^ N) q N ≠ 0)

/-- Full bilateral regularity implies regularity on each finite interval. -/
lemma regularThrough_of_qBilateralRegular {a b : List ℂ} {q : ℂ} (hq0 : q ≠ 0)
    (hq : ‖q‖ < 1) (hB : QBilateralRegular a b q) (N : ℕ) : RegularThrough a b q N := by
  exact ⟨fun x hx => qPochhammer_ne_zero_of_mem_qDenominatorRegular hq hB.1 hx N,
    fun x hx => qPochhammer_div_pow_ne_zero hq0 (hB.2 x hx) N⟩

/-- Nonvanishing of a negative-index prefix implies nonvanishing of every shorter suffix. -/
lemma qPochhammer_div_pow_ne_zero_of_le {x q : ℂ} (hq0 : q ≠ 0) {m N : ℕ} (hm : m ≤ N)
    (hN : qPochhammer (x / q ^ N) q N ≠ 0) : qPochhammer (x / q ^ m) q m ≠ 0 := by
  have hpow : q ^ (N - m) * q ^ m = q ^ N := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  have harg : x / q ^ N * q ^ (N - m) = x / q ^ m := by
    rw [← hpow]
    field_simp
  have H := qPochhammer_add (x / q ^ N) q (N - m) m
  rw [Nat.sub_add_cancel hm, harg] at H
  rw [H] at hN
  exact right_ne_zero_of_mul hN

/-- Finite bilateral term continuity needs regularity only on the retained interval. -/
lemma continuousAt_qPsiTerm_of_regularThrough {a b : List (ℂ → ℂ)} {z : ℂ → ℂ} {x : ℂ}
    {q : ℂ} (hq0 : q ≠ 0) (ha : ∀ f ∈ a, ContinuousAt f x)
    (hb : ∀ f ∈ b, ContinuousAt f x) (hz : ContinuousAt z x) (hz0 : z x ≠ 0)
    (N : ℕ) (hreg : RegularThrough (a.map fun f => f x) (b.map fun f => f x) q N)
    (k : ℤ) (hk : -(N : ℤ) ≤ k ∧ k ≤ N) :
    ContinuousAt (fun y => qPsiTerm (a.map fun f => f y) (b.map fun f => f y) q (z y) k) x := by
  have hnonzero (l : List ℂ) (n : ℕ) (hl : ∀ u ∈ l, qPochhammer u q n ≠ 0) :
      qPochhammerList l q n ≠ 0 := by
    apply List.prod_ne_zero
    simp only [List.mem_map, not_exists, not_and]
    intro u hu he
    exact hl u hu he
  cases k with
  | ofNat j =>
    simp only [Int.ofNat_eq_natCast] at hk
    have hj : j ≤ N := by omega
    have hd : qPochhammerList (b.map fun f => f x) q j ≠ 0 :=
      hnonzero _ j fun u hu => qPochhammer_ne_zero_of_le (hreg.1 u hu) hj
    simp only [Int.ofNat_eq_natCast, qPsiTerm, qPochhammerListInt_natCast,
      qPsiExponent, List.length_map]
    exact (((continuousAt_qPochhammerList ha q j).div₀
      (continuousAt_qPochhammerList hb q j) hd).fun_mul continuousAt_const).fun_mul
      (hz.zpow₀ _ (Or.inl hz0))
  | negSucc j =>
    have hj : j + 1 ≤ N := by omega
    have hp (l : List (ℂ → ℂ)) (hl : ∀ f ∈ l, ContinuousAt f x) :
        ContinuousAt (fun y => qPochhammerList
          ((l.map fun f => f y).map fun u => u * q ^ (-((j : ℤ) + 1))) q (j + 1)) x := by
      have hc : ∀ f ∈ l.map (fun f => fun y => f y * q ^ (-((j : ℤ) + 1))),
          ContinuousAt f x := by
        intro f hf
        rcases List.mem_map.mp hf with ⟨g, hg, rfl⟩
        exact (hl g hg).fun_mul continuousAt_const
      simpa only [List.map_map, Function.comp_def] using
        continuousAt_qPochhammerList hc q (j + 1)
    have hd : qPochhammerList ((a.map fun f => f x).map
        fun u => u * q ^ (-((j : ℤ) + 1))) q (j + 1) ≠ 0 := by
      apply hnonzero
      intro u hu
      rcases List.mem_map.mp hu with ⟨v, hv, rfl⟩
      rw [show v * q ^ (-((j : ℤ) + 1)) = v / q ^ (j + 1) by
        rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by push_cast; rfl,
          zpow_neg, zpow_natCast, div_eq_mul_inv]]
      exact qPochhammer_div_pow_ne_zero_of_le hq0 hj (hreg.2 v hv)
    simp only [qPsiTerm_negSucc, qPsiExponent, List.length_map]
    exact (((hp b hb).div₀ (hp a ha) hd).fun_mul continuousAt_const).fun_mul
      (hz.zpow₀ _ (Or.inl hz0))

/-- Doubly terminating bilateral series are continuous on their finite regularity domain.
No exclusion is imposed on upper products beyond the retained interval. -/
lemma continuousAt_qPsi_finite_of_regularThrough {a b : List (ℂ → ℂ)} {z : ℂ → ℂ} {x : ℂ}
    {q : ℂ} (hq0 : q ≠ 0) (ha : ∀ f ∈ a, ContinuousAt f x)
    (hb : ∀ f ∈ b, ContinuousAt f x) (hz : ContinuousAt z x) (hz0 : z x ≠ 0) (N : ℕ)
    (hreg : RegularThrough (q ^ (-(N : ℤ)) :: a.map fun f => f x)
      (q ^ (N + 1) :: b.map fun f => f x) q N) :
    ContinuousAt (fun y => qPsi (q ^ (-(N : ℤ)) :: a.map fun f => f y)
      (q ^ (N + 1) :: b.map fun f => f y) q (z y)) x := by
  simp_rw [qPsi_eq_sum_Icc hq0 N N]
  change Tendsto _ (𝓝 x) (𝓝 _)
  apply tendsto_finsetSum
  intro k hk
  have hA : ∀ f ∈ (fun _ : ℂ => q ^ (-(N : ℤ))) :: a, ContinuousAt f x := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact continuousAt_const
    · exact ha f hf
  have hB : ∀ f ∈ (fun _ : ℂ => q ^ (N + 1)) :: b, ContinuousAt f x := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact continuousAt_const
    · exact hb f hf
  simpa only [List.map_cons] using
    (continuousAt_qPsiTerm_of_regularThrough hq0 hA hB hz hz0 N hreg k
      (Finset.mem_Icc.mp hk)).tendsto

/-- A negative integer index gives the inverse of an ordinary shifted-factorial product. -/
lemma qPochhammerListInt_neg_natCast (a : List ℂ) (q : ℂ) (k : ℕ) :
    qPochhammerListInt a q (-(k : ℤ)) =
      (qPochhammerList (a.map fun x => x * q ^ (-(k : ℤ))) q k)⁻¹ := by
  have hP (x : ℂ) : qPochhammerInt x q (-(k : ℤ)) =
      (qPochhammer (x * q ^ (-(k : ℤ))) q k)⁻¹ := by
    cases k with
    | zero => simp [qPochhammerInt]
    | succ j =>
      simpa only [Nat.cast_add, Nat.cast_one, Int.negSucc_eq] using
        qPochhammerInt_negSucc x q j
  induction a with
  | nil => simp [qPochhammerListInt, qPochhammerList]
  | cons x a ih =>
    simp only [qPochhammerListInt, qPochhammerList, List.map_cons,
      List.prod_cons, hP, mul_inv] at ih ⊢
    rw [ih]

/-- Equal-length lists have a negative-shift quotient with no residual quadratic q-power.
-/
lemma qPochhammerList_shift_negative_ratio {a b : List ℂ} {q : ℂ} (hq0 : q ≠ 0)
    (hlen : a.length = b.length) (ha : ∀ x ∈ a, x ≠ 0) (hb : ∀ x ∈ b, x ≠ 0) (k : ℕ) :
    qPochhammerList (b.map fun x => x * q ^ (-(k : ℤ))) q k /
        qPochhammerList (a.map fun x => x * q ^ (-(k : ℤ))) q k =
      qPochhammerList (b.map fun x => q / x) q k /
        qPochhammerList (a.map fun x => q / x) q k * (b.prod / a.prod) ^ k := by
  induction a generalizing b with
  | nil =>
    have hb' : b = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst b
    simp [qPochhammerList]
  | cons x a ih =>
    cases b with
    | nil => simp at hlen
    | cons y b =>
      have hlen' : a.length = b.length := by simpa using hlen
      have H := ih hlen' (fun u hu => ha u (by simp [hu]))
        (fun u hu => hb u (by simp [hu]))
      have hx := ha x (by simp)
      have hy := hb y (by simp)
      simp only [qPochhammerList, List.map_cons, List.prod_cons] at H ⊢
      rw [mul_div_mul_comm, qPochhammer_shift_negative_ratio hy hx hq0 k, H]
      simp only [mul_div_mul_comm, mul_pow]
      ring

/-- Reflection of an equal-order bilateral term interchanges reciprocal parameter lists.
The identity retains totalized zeros of finite shifted products. -/
lemma qPsiTerm_reflect {a b : List ℂ} {q z : ℂ} (hq0 : q ≠ 0)
    (hlen : a.length = b.length) (ha : ∀ x ∈ a, x ≠ 0) (hb : ∀ x ∈ b, x ≠ 0) (k : ℕ) :
    qPsiTerm a b q z (-(k : ℤ)) =
      qPsiTerm (b.map fun x => q / x) (a.map fun x => q / x) q
        (b.prod / (a.prod * z)) (k : ℤ) := by
  have he : qPsiExponent a b = 0 := by simp [qPsiExponent, hlen]
  have he' : qPsiExponent (b.map fun x => q / x) (a.map fun x => q / x) = 0 := by
    simp [qPsiExponent, hlen]
  simp only [qPsiTerm, he, he', zpow_zero, mul_one, qPochhammerListInt_neg_natCast,
    qPochhammerListInt_natCast, inv_div_inv]
  rw [qPochhammerList_shift_negative_ratio hq0 hlen ha hb k]
  simp only [zpow_natCast, zpow_neg, ← inv_pow, mul_assoc, ← mul_pow]
  congr 2
  ring

/-- Finite shifted-product inverses are bounded uniformly in both shift and length whenever
the corresponding infinite product is nonzero. -/
lemma exists_norm_inv_qPochhammer_shift_le {z q : ℂ} (hq : ‖q‖ < 1)
    (hz : qPochhammerInf z q ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M k : ℕ, ‖(qPochhammer (z * q ^ M) q k)⁻¹‖ ≤ C := by
  obtain ⟨B, hB⟩ := RamanujanPsi.exists_norm_inv_qPochhammer_le hq hz
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let E := Real.exp (‖z‖ / (1 - ‖q‖))
  have hprefix (M : ℕ) : qPochhammer z q M ≠ 0 := by
    intro he
    apply hz
    rw [qPochhammerInf_mul_qPochhammer hq M, he, zero_mul]
  refine ⟨E * B, by positivity, ?_⟩
  intro M k
  have hM := hprefix M
  have hMk := hprefix (M + k)
  have he : (qPochhammer (z * q ^ M) q k)⁻¹ =
      qPochhammer z q M * (qPochhammer z q (M + k))⁻¹ := by
    rw [qPochhammer_add]
    field_simp
  rw [he, norm_mul]
  exact mul_le_mul (norm_qPochhammer_le_exp hq M) (hB (M + k))
    (norm_nonneg _) (by positivity)

/-- A finite list of shifted factorials tends to the corresponding infinite product. -/
lemma tendsto_qPochhammerList (a : List ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Tendsto (fun k : ℕ => qPochhammerList a q k) atTop (𝓝 (qPochhammerListInf a q)) := by
  induction a with
  | nil => simp only [qPochhammerList, qPochhammerListInf, List.map_nil, List.prod_nil]
           exact tendsto_const_nhds
  | cons x a ih =>
    simpa only [qPochhammerList, qPochhammerListInf, List.map_cons, List.prod_cons] using
      (tendsto_qPochhammer (w := x) hq).mul ih

/-- Regular lower parameters have a nonzero product of infinite shifted factorials. -/
lemma qPochhammerListInf_ne_zero {b : List ℂ} {q : ℂ} (hq : ‖q‖ < 1)
    (hb : QDenominatorRegular b q) : qPochhammerListInf b q ≠ 0 := by
  apply List.prod_ne_zero
  simp only [List.mem_map, not_exists, not_and]
  intro x hx he
  apply qPochhammerInf_ne_zero hq (fun j => sub_ne_zero.mpr (Ne.symm (hb x hx j))) he

/-- A quotient of fixed finite products is uniformly bounded when its lower parameters are
regular in the open unit disk. -/
lemma exists_norm_qPochhammerList_ratio_le (a : List ℂ) {b : List ℂ} {q : ℂ}
    (hq : ‖q‖ < 1) (hb : QDenominatorRegular b q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖qPochhammerList a q k / qPochhammerList b q k‖ ≤ C := by
  have H := (tendsto_qPochhammerList a hq).div (tendsto_qPochhammerList b hq)
    (qPochhammerListInf_ne_zero hq hb)
  obtain ⟨C, hC⟩ := H.norm.bddAbove_range
  have hbound (k : ℕ) : ‖qPochhammerList a q k / qPochhammerList b q k‖ ≤ C := hC ⟨k, rfl⟩
  exact ⟨C, (norm_nonneg _).trans (hbound 0), hbound⟩

/-- Upper parameters avoiding the positive q-lattice give regular reciprocal lower parameters.
-/
lemma qDenominatorRegular_reciprocal {a : List ℂ} {q : ℂ} (ha0 : ∀ x ∈ a, x ≠ 0)
    (ha : ∀ x ∈ a, ∀ j : ℕ, x ≠ q ^ (j + 1)) :
    QDenominatorRegular (a.map fun x => q / x) q := by
  intro x hx j he
  rcases List.mem_map.mp hx with ⟨u, hu, rfl⟩
  have hu0 := ha0 u hu
  have hpow : q * q ^ j = u := by field_simp at he; exact he
  apply ha u hu j
  rw [pow_succ]
  linear_combination -hpow

end DLMF.QHypergeometric.FiniteBilateral
