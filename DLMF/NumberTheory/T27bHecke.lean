/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Functions

/-!
# Hecke multiplication formulas (helpers for DLMF 27.14.19)

For a multiplicative `f : ℕ → R` and a completely multiplicative weight `w`, the Hecke relation
`f(m) f(n) = ∑_{d ∣ (m,n)} w(d) f(mn/d²)` (the shape of DLMF 27.3.7 and 27.14.19) reduces to prime
powers (`t27b_hecke_mul`), and at a prime power it follows from the two-term recurrence
`f(p^{r+2}) = f(p) f(p^{r+1}) - w(p) f(p^r)` (`t27b_hecke_prime_pow`). Used for Ramanujan's `τ` in
`DLMF.NumberTheory.Partitions`; the reduction follows `s27_sigmaC_mul_sigmaC`
(`DLMF.NumberTheory.Functions`), here stated for general `f` and `w`.
-/

@[expose] public noncomputable section

open Finset

namespace DLMF.NumberTheory

/-- Hecke product formula for a sequence with `g 0 = 1` and
`g (r + 2) = g 1 * g (r + 1) - c * g r`. -/
theorem t27b_hecke_rec {R : Type*} [CommRing R] (g : ℕ → R) (c : R) (h0 : g 0 = 1)
    (hrec : ∀ r, g (r + 2) = g 1 * g (r + 1) - c * g r) :
    ∀ a b : ℕ, a ≤ b → g a * g b = ∑ k ∈ range (a + 1), c ^ k * g (a + b - 2 * k) := by
  have h1 : ∀ b, 1 ≤ b → g 1 * g b = g (b + 1) + c * g (b - 1) := by
    intro b hb
    obtain ⟨r, rfl⟩ : ∃ r, b = r + 1 := ⟨b - 1, by omega⟩
    rw [hrec r]; simp
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b hab
  match a, ih with
  | 0, _ => simp [h0]
  | 1, _ =>
    rw [h1 b hab]
    simp [sum_range_succ, add_comm]
  | a + 2, ih =>
    have hA := ih (a + 1) (by omega) b (by omega)
    have hB := ih a (by omega) b (by omega)
    rw [hrec a, sub_mul, mul_assoc, hA, mul_assoc, hB, mul_sum, mul_sum]
    have hC : ∀ k ∈ range (a + 1 + 1), g 1 * (c ^ k * g (a + 1 + b - 2 * k)) =
        c ^ k * g (a + 2 + b - 2 * k) + c ^ (k + 1) * g (a + b - 2 * k) := by
      intro k hk
      have hk' := mem_range.mp hk
      rw [mul_left_comm, h1 _ (by omega), pow_succ,
        show a + 1 + b - 2 * k + 1 = a + 2 + b - 2 * k by omega,
        show a + 1 + b - 2 * k - 1 = a + b - 2 * k by omega]
      ring
    have hD : ∀ k ∈ range (a + 1), c * (c ^ k * g (a + b - 2 * k)) =
        c ^ (k + 1) * g (a + b - 2 * k) := fun k _ ↦ by ring
    rw [sum_congr rfl hC, sum_add_distrib, sum_congr rfl hD,
      sum_range_succ (fun k ↦ c ^ (k + 1) * g (a + b - 2 * k)) (a + 1),
      sum_range_succ (fun k ↦ c ^ k * g (a + 2 + b - 2 * k)) (a + 2),
      show a + b - 2 * (a + 1) = a + 2 + b - 2 * (a + 2) by omega]
    ring

/-- The Hecke relation for `f` at prime powers,
`f(pᵃ) f(pᵇ) = ∑_{d ∣ p^min(a,b)} w(d) f(p^{a+b}/d²)`, when `f(p^j)` satisfies
`f(p^{r+2}) = f(p) f(p^{r+1}) - w(p) f(p^r)`. -/
theorem t27b_hecke_prime_pow {R : Type*} [CommRing R] (f w : ℕ → R) {p : ℕ} (hp : p.Prime)
    (hw : ∀ k, w (p ^ k) = w p ^ k) (h0 : f 1 = 1)
    (hrec : ∀ r, f (p ^ (r + 2)) = f p * f (p ^ (r + 1)) - w p * f (p ^ r)) (a b : ℕ) :
    f (p ^ a) * f (p ^ b) =
      ∑ d ∈ (p ^ min a b).divisors, w d * f (p ^ (a + b) / d ^ 2) := by
  wlog hab : a ≤ b generalizing a b
  · rw [min_comm, add_comm, mul_comm]; exact this b a (by omega)
  have H := t27b_hecke_rec (fun j ↦ f (p ^ j)) (w p) (by simpa using h0)
    (fun r ↦ by simpa using hrec r) a b hab
  rw [H, min_eq_left hab, Nat.sum_divisors_prime_pow hp]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ a := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [hw, ← pow_mul, Nat.pow_div (by omega) hp.pos, mul_comm k 2]


/-- Splitting off the `p`-part of `∑_{d ∣ (m,n)} w(d) f(mn/d²)` for multiplicative `f` and
completely multiplicative `w`. -/
theorem t27b_hecke_split {R : Type*} [CommRing R] {f w : ℕ → R} (hf : IsMultiplicativeFn f)
    (hw : ∀ i j, w (i * j) = w i * w j) {p a b m' n' : ℕ} (hp : 0 < p) (hm : p.Coprime m')
    (hn : p.Coprime n') (hm0 : 0 < m') (hn0 : 0 < n') :
    ∑ d ∈ ((p ^ a * m').gcd (p ^ b * n')).divisors,
        w d * f (p ^ a * m' * (p ^ b * n') / d ^ 2) =
      (∑ i ∈ (p ^ min a b).divisors, w i * f (p ^ (a + b) / i ^ 2)) *
        ∑ j ∈ (m'.gcd n').divisors, w j * f (m' * n' / j ^ 2) := by
  have hcop : (p ^ min a b).Coprime (m'.gcd n') :=
    Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left m' n') hm)
  rw [s27_gcd_split hm hn, Nat.divisors_mul, Finset.mul_def,
    sum_image (Nat.Coprime.mul_injOn_divisors hcop), sum_product, sum_mul_sum]
  refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
  have hi' : i ∣ p ^ min a b := Nat.dvd_of_mem_divisors hi
  have hj' : j ∣ m'.gcd n' := Nat.dvd_of_mem_divisors hj
  have hi2 : i ^ 2 ∣ p ^ (a + b) :=
    (pow_dvd_pow_of_dvd hi' 2).trans (by rw [← pow_mul]; exact Nat.pow_dvd_pow p (by omega))
  have hj2 : j ^ 2 ∣ m' * n' := by
    rw [sq]
    exact mul_dvd_mul (hj'.trans (Nat.gcd_dvd_left _ _)) (hj'.trans (Nat.gcd_dvd_right _ _))
  have hnum : p ^ a * m' * (p ^ b * n') / (i * j) ^ 2 =
      p ^ (a + b) / i ^ 2 * (m' * n' / j ^ 2) := by
    rw [Nat.div_mul_div_comm hi2 hj2, mul_pow]
    congr 1
    rw [pow_add]; ring
  have hc : (p ^ (a + b) / i ^ 2).Coprime (m' * n' / j ^ 2) := by
    have : (p ^ (a + b)).Coprime (m' * n') :=
      Nat.Coprime.pow_left _ (Nat.Coprime.mul_right hm hn)
    exact (this.coprime_dvd_left (Nat.div_dvd_of_dvd hi2)).coprime_dvd_right
      (Nat.div_dvd_of_dvd hj2)
  have hpos1 : 0 < p ^ (a + b) / i ^ 2 :=
    Nat.div_pos (Nat.le_of_dvd (pow_pos hp _) hi2) (pow_pos (Nat.pos_of_dvd_of_pos hi'
      (pow_pos hp _)) 2)
  have hpos2 : 0 < m' * n' / j ^ 2 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hm0 hn0) hj2) (pow_pos (Nat.pos_of_dvd_of_pos hj'
      (Nat.gcd_pos_of_pos_left _ hm0)) 2)
  rw [hnum, hf.2 _ _ hpos1 hpos2 hc, hw]
  ring

/-- Hecke multiplication formula `f(m) f(n) = ∑_{d ∣ (m,n)} w(d) f(mn/d²)` for multiplicative
`f` satisfying it at prime powers, with `w` completely multiplicative. -/
theorem t27b_hecke_mul {R : Type*} [CommRing R] {f w : ℕ → R} (hf : IsMultiplicativeFn f)
    (hw : ∀ i j, w (i * j) = w i * w j)
    (hpp : ∀ p, p.Prime → ∀ a b : ℕ, f (p ^ a) * f (p ^ b) =
      ∑ d ∈ (p ^ min a b).divisors, w d * f (p ^ (a + b) / d ^ 2))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    f m * f n = ∑ d ∈ (m.gcd n).divisors, w d * f (m * n / d ^ 2) := by
  induction h : m * n using Nat.strong_induction_on generalizing m n with
  | _ N ih =>
  rw [← h]
  rcases Nat.lt_or_ge (m * n) 2 with hlt | hge
  · have hm1 : m = 1 := by nlinarith
    have hn1 : n = 1 := by nlinarith
    subst hm1 hn1
    have hw1 : w 1 = 1 := by
      have := hpp 2 Nat.prime_two 0 0
      simpa [hf.1] using this.symm
    simp [hf.1, hw1]
  set p := (m * n).minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpmn : p ∣ m * n := Nat.minFac_dvd _
  set a := m.factorization p
  set b := n.factorization p
  set m' := m / p ^ a
  set n' := n / p ^ b
  have hmm : p ^ a * m' = m := Nat.ordProj_mul_ordCompl_eq_self m p
  have hnn : p ^ b * n' = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hcm : p.Coprime m' := Nat.coprime_ordCompl hp hm.ne'
  have hcn : p.Coprime n' := Nat.coprime_ordCompl hp hn.ne'
  have hm' : 0 < m' := Nat.pos_of_ne_zero fun h0 ↦ by rw [h0, mul_zero] at hmm; omega
  have hn' : 0 < n' := Nat.pos_of_ne_zero fun h0 ↦ by rw [h0, mul_zero] at hnn; omega
  have hab : 1 ≤ a + b := by
    rcases (Nat.Prime.dvd_mul hp).mp hpmn with h1 | h1
    · have := hp.factorization_pos_of_dvd hm.ne' h1; omega
    · have := hp.factorization_pos_of_dvd hn.ne' h1; omega
  have hlt : m' * n' < N := by
    rw [← h, ← hmm, ← hnn]
    have hpow : 2 ≤ p ^ a * p ^ b := by
      rw [← pow_add]
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (a + b) := Nat.pow_le_pow_right hp.pos hab
    have : 0 < m' * n' := Nat.mul_pos hm' hn'
    nlinarith
  have ih' := ih (m' * n') hlt hm' hn' rfl
  rw [← hmm, ← hnn, t27b_hecke_split hf hw hp.pos hcm hcn hm' hn', ← ih', ← hpp p hp,
    hf.2 _ _ (pow_pos hp.pos _) hm' (Nat.Coprime.pow_left a hcm),
    hf.2 _ _ (pow_pos hp.pos _) hn' (Nat.Coprime.pow_left b hcn)]
  ring
end DLMF.NumberTheory
