/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.WignerSymbols.Basic
public import DLMF.Hypergeometric.Basic.Pochhammer

/-!
# Reciprocal factorials as Pochhammer symbols

Racah's sums for the `3j` and `6j` symbols are finite sums of products of reciprocal factorials
`ratInvFactorial`, which vanish at negative arguments. After the substitution of natural-number
parameters each factor is a Pochhammer symbol in the summation index, and the sums become
terminating hypergeometric series with cleared denominators
(`DLMF.Hypergeometric.genClearedFiniteHG`).

## Main results

* `ratInvFactorial_natCast_sub_natCast`: `1/(N - k)! = (-1)ᵏ (-N)ₖ / N!` for all `k`.
* `ratInvFactorial_intCast_add_natCast`: `1/(c + k)! = (c + 1 + k)_{n-k} / (c + n)!` for `k ≤ n` and
  `c + n ≥ 0`, including the vanishing terms `c + k < 0`.
* `natCast_factorial_sub_eq_pochhammer`: `(M - k)! = (-1)^{n-k} (M - n)! (-M + k)_{n-k}`.
-/

@[expose] public noncomputable section

open DLMF.Hypergeometric

namespace DLMF.WignerSymbols

/-- `1/(N - k)! = (-1)ᵏ (-N)ₖ / N!`; both sides vanish for `k > N`. -/
theorem ratInvFactorial_natCast_sub_natCast (N k : ℕ) :
    (ratInvFactorial ((N : ℚ) - k) : ℂ) = (-1) ^ k * pochhammer (-(N : ℂ)) k / N.factorial := by
  by_cases hk : k ≤ N
  · rw [ratInvFactorial_of_eq (n := N - k) (by push_cast [hk]; ring), pochhammer_neg_coe_nat,
      ← Nat.factorial_mul_descFactorial hk]
    have h1 : ((N - k).factorial : ℂ) ≠ 0 := by exact_mod_cast (N - k).factorial_ne_zero
    have h2 : (N.descFactorial k : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hk).ne'
    have hs : ((-1 : ℂ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    push_cast
    field_simp
    linear_combination -hs
  · push Not at hk
    have hlt : (N : ℚ) < k := by exact_mod_cast hk
    rw [ratInvFactorial_of_neg (by linarith), pochhammer_neg_nat_eq_zero hk]
    simp

/-- `(m + 1)_j m! = (m + j)!`. -/
private theorem pochhammer_natCast_add_one_mul_factorial (m j : ℕ) :
    pochhammer ((m : ℂ) + 1) j * m.factorial = ((m + j).factorial : ℂ) := by
  induction j with
  | zero => simp [pochhammer_zero]
  | succ j ih =>
    rw [pochhammer_succ, mul_right_comm, ih, ← add_assoc, Nat.factorial_succ]
    push_cast
    ring

/-- `1/(c + k)! = (c + 1 + k)_{n-k} / (c + n)!` for `k ≤ n` and `c + n ≥ 0`; both sides vanish
for `c + k < 0`. -/
theorem ratInvFactorial_intCast_add_natCast (c : ℤ) {n k : ℕ} (hk : k ≤ n) (hc : 0 ≤ c + n) :
    (ratInvFactorial ((c : ℚ) + k) : ℂ) =
      pochhammer ((c : ℂ) + 1 + k) (n - k) / ((c + n).toNat).factorial := by
  by_cases hck : 0 ≤ c + k
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hck
    have hcn : (c + n).toNat = m + (n - k) := by omega
    rw [ratInvFactorial_of_eq (n := m) (by exact_mod_cast hm), hcn,
      ← pochhammer_natCast_add_one_mul_factorial m (n - k)]
    have hmc : (c : ℂ) + 1 + k = (m : ℂ) + 1 := by
      have : ((c + k : ℤ) : ℂ) = (m : ℂ) := by exact_mod_cast hm
      push_cast at this; linear_combination this
    rw [hmc]
    have h1 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    by_cases hp : pochhammer ((m : ℂ) + 1) (n - k) = 0
    · exfalso
      rw [pochhammer, ascPochhammer_eval_eq_zero_iff] at hp
      obtain ⟨i, -, hi⟩ := hp
      have : ((i + m + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination hi
      exact absurd (by exact_mod_cast this : i + m + 1 = 0) (by omega)
    push_cast
    field_simp
  · push Not at hck
    rw [ratInvFactorial_of_neg (by exact_mod_cast hck)]
    have hp : pochhammer ((c : ℂ) + 1 + k) (n - k) = 0 := by
      rw [pochhammer, ascPochhammer_eval_eq_zero_iff]
      refine ⟨(-(c + 1 + k)).toNat, by omega, ?_⟩
      have h0 : (((-(c + 1 + k)).toNat : ℤ) : ℂ) = ((-(c + 1 + k) : ℤ) : ℂ) := by
        rw [Int.toNat_of_nonneg (by omega)]
      push_cast at h0 ⊢
      linear_combination h0
    rw [hp]
    simp

/-- `(M - k)! = (-1)^{n-k} (M - n)! (-M + k)_{n-k}` for `k ≤ n ≤ M`. -/
theorem natCast_factorial_sub_eq_pochhammer {M n k : ℕ} (hk : k ≤ n) (hn : n ≤ M) :
    ((M - k).factorial : ℂ) = (-1) ^ (n - k) * (M - n).factorial *
        pochhammer (-(M : ℂ) + k) (n - k) := by
  have e : -(M : ℂ) + k = -((M - k : ℕ) : ℂ) := by rw [Nat.cast_sub (hk.trans hn)]; ring
  have hf := Nat.factorial_mul_descFactorial (show n - k ≤ M - k by omega)
  rw [show M - k - (n - k) = M - n by omega] at hf
  have hs : ((-1 : ℂ) ^ (n - k)) ^ 2 = 1 := by rw [← pow_mul, pow_mul']; norm_num
  rw [e, pochhammer_neg_coe_nat, ← hf, Nat.cast_mul,
    show (-1 : ℂ) ^ (n - k) * ((M - n).factorial : ℂ) * ((-1) ^ (n - k) *
      ((M - k).descFactorial (n - k) : ℂ)) = ((-1 : ℂ) ^ (n - k)) ^ 2 *
        (((M - n).factorial : ℂ) * ((M - k).descFactorial (n - k) : ℂ)) by ring, hs, one_mul]

end DLMF.WignerSymbols
