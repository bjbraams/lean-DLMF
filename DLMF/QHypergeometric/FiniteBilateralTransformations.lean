/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bailey
public import DLMF.QHypergeometric.BilateralTransformations

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

end DLMF.QHypergeometric.FiniteBilateral
