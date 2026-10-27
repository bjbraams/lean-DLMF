/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QSeries.Identities
public import DLMF.QSeries.Saalschutz

/-!
# Bailey chains (AAR Chapter 12)

Rogers–Ramanujan identities, Bailey's lemma, and Watson's transformation are absent from
Mathlib. All three are proved here from the `q`-Pfaff–Saalschütz sum (`DLMF.QSeries.Saalschutz`).

* Bailey's lemma (`bailey_lemma`) reduces, after interchanging the double sum, to a shifted
  `q`-Pfaff–Saalschütz sum (`bailey_inner`); `bailey_relation` is its form at a fixed index with
  hypotheses only up to that index.
* The unit Bailey pair (`unit_pair`) is proved by an explicit telescoping certificate.
  Watson's transformation of a terminating very-well-poised `₈φ₇` into a balanced `₄φ₃`
  (`watson_transformation`) follows from two applications of Bailey's lemma to it; the values of
  `a` with `(aq;q)_{2n} = 0` that the hypotheses allow are reached by continuity in `a`.
* The limiting form of Bailey's lemma (`ρ₁, ρ₂ → ∞`, `bailey_limit_relation`) rests on the
  identity `∑_m [N m]_q q^{m(m-1)} A^m (Aq^m;q)_{N-m} = 1` (`sum_qBinom_limit`). Applied twice to
  the unit pair and with `n → ∞` (Tannery's theorem), it gives
  `∑ a^k q^{k²}/(q;q)_k = (aq;q)_∞⁻¹ ∑ a^{2k} q^{2k²} α_k` (`sum_unit_bailey`). At `a = 1` and
  `a = q` the right side is the Jacobi triple product at base `q⁵`, and regrouping
  `(q;q)_∞ = (q, q², q³, q⁴, q⁵; q⁵)_∞` (`qPochhammerInf_mod_five`) gives the Rogers–Ramanujan
  identities.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

open DLMF.QSeries Finset Filter
open scoped Topology

namespace DLMF.Bailey

/-! ### The limiting form of Bailey's lemma (`ρ₁, ρ₂ → ∞`) -/

private lemma mul_pred_add (m : ℕ) : m * (m - 1) + m = m * m := by
  rcases m with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]; ring

/-- The summand of the limiting `q`-Pfaff–Saalschütz identity. -/
private def limTerm (q A : ℂ) (N m : ℕ) : ℂ :=
  qBinom q N m * q ^ (m * (m - 1)) * A ^ m * qPochhammer (A * q ^ m) q (N - m)

private def limCert (q A : ℂ) (N : ℕ) : ℕ → ℂ
  | 0 => 0
  | k + 1 => -(A ^ (k + 1) * q ^ (k * k + N) * qBinom q N k * qPochhammer (A * q ^ k) q (N - k))

private lemma lim_step (q A : ℂ) (N m : ℕ) (hm : m ≤ N + 1) :
    limTerm q A (N + 1) m - limTerm q A N m = limCert q A N (m + 1) - limCert q A N m := by
  rcases m with _ | k
  · simp only [limTerm, limCert, qBinom_zero_right, Nat.zero_mul, pow_zero, mul_one,
      Nat.sub_zero, zero_add, pow_one, sub_zero, Nat.zero_sub]
    rw [qPochhammer_succ]
    ring
  rcases eq_or_lt_of_le hm with h | h
  · obtain rfl : k = N := by omega
    simp only [limTerm, limCert]
    rw [qBinom_eq_zero_of_lt q (Nat.lt_succ_self k), qBinom_self, qBinom_self, Nat.sub_self,
      Nat.sub_self, show (k + 1) * (k + 1 - 1) = k * k + k by simp; ring]
    simp only [qPochhammer_zero]
    ring
  obtain ⟨r, rfl⟩ : ∃ r, N = k + 1 + r := ⟨N - (k + 1), by omega⟩
  have hP1 := qBinom_succ_succ q (k + 1 + r) k
  have hP2 := qBinom_succ_succ' q (k + 1 + r) k
  rw [show k + 1 + r - k = r + 1 by omega] at hP2
  simp only [limTerm, limCert]
  rw [show k + 1 + r + 1 - (k + 1) = r + 1 by omega, show k + 1 + r - (k + 1) = r by omega,
    show k + 1 + r - k = r + 1 by omega, qPochhammer_succ (A * q ^ (k + 1)) q r,
    qPochhammer_succ' (A * q ^ k) q r, show A * q ^ k * q = A * q ^ (k + 1) by ring,
    show (k + 1) * (k + 1 - 1) = (k + 1) * k by simp,
    show (k + 1) * (k + 1) + (k + 1 + r) = (k + 1) * k + 1 + k + k + (r + 1) by ring,
    show k * k + (k + 1 + r) = (k + 1) * k + (r + 1) by ring]
  linear_combination A ^ (k + 1) * q ^ ((k + 1) * k) * qPochhammer (A * q ^ (k + 1)) q r *
    (-A * q ^ k * q ^ (r + 1) * hP1 + hP2)

/-- The limiting `q`-Pfaff–Saalschütz identity, valid for all `q, A`:
`∑_m [N m]_q q^{m(m-1)} A^m (Aq^m;q)_{N-m} = 1`. -/
theorem sum_qBinom_limit (q A : ℂ) (N : ℕ) :
    ∑ m ∈ range (N + 1), qBinom q N m * q ^ (m * (m - 1)) * A ^ m *
      qPochhammer (A * q ^ m) q (N - m) = 1 := by
  change ∑ m ∈ range (N + 1), limTerm q A N m = 1
  induction N with
  | zero => simp [limTerm]
  | succ N ih =>
    have hsum : ∑ m ∈ range (N + 1 + 1), (limTerm q A (N + 1) m - limTerm q A N m) =
        limCert q A N (N + 1 + 1) - limCert q A N 0 := by
      rw [← sum_range_sub (limCert q A N)]
      exact sum_congr rfl fun m hm => lim_step q A N m (by simp at hm; omega)
    have hlast : limTerm q A N (N + 1) = 0 := by
      simp [limTerm, qBinom_eq_zero_of_lt q (Nat.lt_succ_self N)]
    have hcert : limCert q A N (N + 1 + 1) = 0 := by
      simp [limCert, qBinom_eq_zero_of_lt q (Nat.lt_succ_self N)]
    rw [sum_sub_distrib, sum_range_succ (fun m => limTerm q A N m), hlast, add_zero, ih,
      hcert] at hsum
    simp only [limCert, sub_zero] at hsum
    exact sub_eq_zero.mp hsum

/-- The limiting identity in quotient form. -/
theorem sum_limit_div (q A : ℂ) (N : ℕ) (hq : ∀ m ≤ N, qPochhammer q q m ≠ 0)
    (hA : qPochhammer A q N ≠ 0) :
    ∑ m ∈ range (N + 1), A ^ m * q ^ (m * (m - 1)) /
        (qPochhammer q q (N - m) * qPochhammer q q m * qPochhammer A q m) =
      1 / (qPochhammer q q N * qPochhammer A q N) := by
  rw [eq_div_iff (mul_ne_zero (hq N le_rfl) hA), sum_mul, ← sum_qBinom_limit q A N]
  refine sum_congr rfl fun m hm => ?_
  have hmN : m ≤ N := by simpa [Nat.lt_succ_iff] using hm
  have hqm := hq m hmN
  have hqnm := hq (N - m) (Nat.sub_le N m)
  have hAm := qPochhammer_ne_zero_of_le hA hmN
  have hB := qBinom_mul_qPochhammer q m (N - m)
  have hS := qPochhammer_add A q m (N - m)
  rw [Nat.add_sub_cancel' hmN] at hB hS
  rw [← hB, hS]
  field_simp

/-- The inner sum of the limiting Bailey lemma: for `j ≤ n`,
`∑_{k=j}^n a^k q^{k²} / ((q)_{n-k} (q)_{k-j} (aq)_{k+j}) = a^j q^{j²} / ((q)_{n-j} (aq)_{n+j})`. -/
theorem bailey_limit_inner {a q : ℂ} {n j : ℕ} (hqq : ∀ m ≤ n, qPochhammer q q m ≠ 0)
    (haq : qPochhammer (a * q) q (n + n) ≠ 0) (hj : j ≤ n) :
    ∑ k ∈ Ico j (n + 1), a ^ k * q ^ (k * k) /
        (qPochhammer q q (n - k) * (qPochhammer q q (k - j) * qPochhammer (a * q) q (k + j))) =
      a ^ j * q ^ (j * j) / (qPochhammer q q (n - j) * qPochhammer (a * q) q (n + j)) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hj
  have haq' : ∀ m ≤ j + j + N, qPochhammer (a * q) q m ≠ 0 :=
    fun m hm => qPochhammer_ne_zero_of_le haq (by omega)
  set A := a * q * q ^ (j + j) with hAdef
  have hA : qPochhammer A q N ≠ 0 := by
    have := haq' (j + j + N) le_rfl
    rw [qPochhammer_add] at this
    exact right_ne_zero_of_mul this
  have hS := sum_limit_div q A N (fun m hm => hqq m (by omega)) hA
  rw [sum_Ico_eq_sum_range, show j + N + 1 - j = N + 1 by omega]
  have hterm : ∀ m ∈ range (N + 1),
      a ^ (j + m) * q ^ ((j + m) * (j + m)) /
          (qPochhammer q q (j + N - (j + m)) *
            (qPochhammer q q (j + m - j) * qPochhammer (a * q) q (j + m + j))) =
        a ^ j * q ^ (j * j) / qPochhammer (a * q) q (j + j) *
          (A ^ m * q ^ (m * (m - 1)) /
            (qPochhammer q q (N - m) * qPochhammer q q m * qPochhammer A q m)) := by
    intro m hm
    have hmN : m ≤ N := by simpa [Nat.lt_succ_iff] using hm
    rw [show j + N - (j + m) = N - m by omega, show j + m - j = m by omega,
      show j + m + j = j + j + m by omega, qPochhammer_add (a * q) q (j + j) m]
    have e3 := haq' (j + j + m) (by omega)
    rw [qPochhammer_add] at e3
    have e3a := left_ne_zero_of_mul e3
    have e3b := right_ne_zero_of_mul e3
    have e4 := hqq (N - m) (by omega)
    have e5 := hqq m (by omega)
    have hexp : q ^ ((j + m) * (j + m)) = q ^ (j * j) * (q ^ m * (q ^ (j + j)) ^ m) *
        q ^ (m * (m - 1)) := by
      rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      have := mul_pred_add m
      nlinarith
    rw [hexp, hAdef]
    field_simp
    ring
  rw [sum_congr rfl hterm, ← mul_sum, hS, show j + N - j = N by omega,
    show j + N + j = j + j + N by omega, qPochhammer_add (a * q) q (j + j) N]
  have f3 := haq' (j + j + N) le_rfl
  rw [qPochhammer_add] at f3
  have g5 := left_ne_zero_of_mul f3
  have g6 := right_ne_zero_of_mul f3
  have g7 := hqq N (by omega)
  rw [hAdef]
  field_simp

/-- The limiting form of Bailey's lemma at a fixed index `n` (`ρ₁, ρ₂ → ∞`): if `(α, β)` is a
Bailey pair up to `n`, then
`∑_k a^k q^{k²} β_k / (q)_{n-k} = ∑_k a^k q^{k²} α_k / ((q)_{n-k} (aq)_{n+k})`. -/
theorem bailey_limit_relation {a q : ℂ} {α β : ℕ → ℂ} {n : ℕ}
    (h : ∀ k ≤ n, β k = ∑ j ∈ range (k + 1),
      α j / (qPochhammer q q (k - j) * qPochhammer (a * q) q (k + j)))
    (hqq : ∀ m ≤ n, qPochhammer q q m ≠ 0) (haq : qPochhammer (a * q) q (n + n) ≠ 0) :
    ∑ k ∈ range (n + 1), a ^ k * q ^ (k * k) * β k / qPochhammer q q (n - k) =
      ∑ k ∈ range (n + 1), a ^ k * q ^ (k * k) * α k /
        (qPochhammer q q (n - k) * qPochhammer (a * q) q (n + k)) := by
  set W : ℕ → ℕ → ℂ := fun k j => a ^ k * q ^ (k * k) /
    (qPochhammer q q (n - k) * (qPochhammer q q (k - j) * qPochhammer (a * q) q (k + j)))
    with hW
  have hL : ∀ k ∈ range (n + 1), a ^ k * q ^ (k * k) * β k / qPochhammer q q (n - k) =
      ∑ j ∈ Ico 0 (k + 1), α j * W k j := by
    intro k hk
    rw [h k (by simpa [Nat.lt_succ_iff] using hk), ← range_eq_Ico, mul_sum, sum_div]
    refine sum_congr rfl fun j _ => ?_
    simp only [hW]
    ring
  rw [sum_congr rfl hL, range_eq_Ico, ← sum_Ico_Ico_comm 0 (n + 1) (fun i k => α i * W k i)]
  refine sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := by simp at hi; omega
  rw [← mul_sum, hW]
  simp only
  rw [bailey_limit_inner hqq haq hin]
  ring

/-- A Bailey pair relative to `a`: `β_n = ∑_{k=0}^n α_k / ((q;q)_{n-k} (aq;q)_{n+k})`. -/
@[dlmf 17.12.E3]
def IsBaileyPair (a q : ℂ) (α β : ℕ → ℂ) : Prop :=
  ∀ n : ℕ,
    β n =
      ∑ k ∈ Finset.range (n + 1),
        α k / (qPochhammer q q (n - k) * qPochhammer (a * q) q (n + k))

/-- The inner sum of Bailey's lemma, a shifted `q`-Pfaff–Saalschütz sum: for `j ≤ n`,
`∑_{k=j}^n (ρ₁)_k (ρ₂)_k (x)_{n-k} x^k / ((q)_{n-k} (aq/ρ₁)_n (aq/ρ₂)_n (q)_{k-j} (aq)_{k+j})`
equals `(ρ₁)_j (ρ₂)_j x^j / ((aq/ρ₁)_j (aq/ρ₂)_j (q)_{n-j} (aq)_{n+j})`, with `x = aq/(ρ₁ρ₂)`. -/
theorem bailey_inner {a q ρ1 ρ2 : ℂ} {n j : ℕ} (hρ1 : ρ1 ≠ 0) (hρ2 : ρ2 ≠ 0)
    (hqq : ∀ m ≤ n, qPochhammer q q m ≠ 0) (haq : qPochhammer (a * q) q (n + n) ≠ 0)
    (h1 : qPochhammer (a * q / ρ1) q n ≠ 0) (h2 : qPochhammer (a * q / ρ2) q n ≠ 0)
    (hj : j ≤ n) :
    ∑ k ∈ Ico j (n + 1), qPochhammer ρ1 q k * qPochhammer ρ2 q k *
        qPochhammer (a * q / (ρ1 * ρ2)) q (n - k) * (a * q / (ρ1 * ρ2)) ^ k /
        (qPochhammer q q (n - k) * qPochhammer (a * q / ρ1) q n * qPochhammer (a * q / ρ2) q n *
          (qPochhammer q q (k - j) * qPochhammer (a * q) q (k + j))) =
      qPochhammer ρ1 q j * qPochhammer ρ2 q j * (a * q / (ρ1 * ρ2)) ^ j /
        (qPochhammer (a * q / ρ1) q j * qPochhammer (a * q / ρ2) q j *
          (qPochhammer q q (n - j) * qPochhammer (a * q) q (n + j))) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hj
  have haq' : ∀ m ≤ j + j + N, qPochhammer (a * q) q m ≠ 0 :=
    fun m hm => qPochhammer_ne_zero_of_le haq (by omega)
  set x := a * q / (ρ1 * ρ2) with hx
  set r := ρ1 * q ^ j
  set s := ρ2 * q ^ j
  have hxrs : x * r * s = a * q * q ^ (j + j) := by
    simp only [hx, r, s]; field_simp; ring
  have hxr : x * r = a * q / ρ2 * q ^ j := by simp only [hx, r]; field_simp
  have hxs : x * s = a * q / ρ1 * q ^ j := by simp only [hx, s]; field_simp
  have hA : qPochhammer (x * r * s) q N ≠ 0 := by
    rw [hxrs]
    have := haq' (j + j + N) le_rfl
    rw [qPochhammer_add] at this
    exact right_ne_zero_of_mul this
  have hS := sum_saalschutz_div q x r s N (fun m hm => hqq m (by omega)) hA
  rw [sum_Ico_eq_sum_range, show j + N + 1 - j = N + 1 by omega]
  have hterm : ∀ m ∈ range (N + 1),
      qPochhammer ρ1 q (j + m) * qPochhammer ρ2 q (j + m) *
          qPochhammer x q (j + N - (j + m)) * x ^ (j + m) /
          (qPochhammer q q (j + N - (j + m)) * qPochhammer (a * q / ρ1) q (j + N) *
            qPochhammer (a * q / ρ2) q (j + N) *
            (qPochhammer q q (j + m - j) * qPochhammer (a * q) q (j + m + j))) =
        qPochhammer ρ1 q j * qPochhammer ρ2 q j * x ^ j /
            (qPochhammer (a * q / ρ1) q (j + N) * qPochhammer (a * q / ρ2) q (j + N) *
              qPochhammer (a * q) q (j + j)) *
          (qPochhammer r q m * qPochhammer s q m * qPochhammer x q (N - m) * x ^ m /
            (qPochhammer q q (N - m) * qPochhammer q q m * qPochhammer (x * r * s) q m)) := by
    intro m hm
    have hmN : m ≤ N := by simpa [Nat.lt_succ_iff] using hm
    rw [show j + N - (j + m) = N - m by omega, show j + m - j = m by omega,
      show j + m + j = j + j + m by omega, qPochhammer_add ρ1 q j m,
      qPochhammer_add ρ2 q j m, qPochhammer_add (a * q) q (j + j) m, hxrs, pow_add]
    have e3 := haq' (j + j + m) (by omega)
    rw [qPochhammer_add] at e3
    have e3a := left_ne_zero_of_mul e3
    have e3b := right_ne_zero_of_mul e3
    have e4 := hqq (N - m) (by omega)
    have e5 := hqq m (by omega)
    field_simp
    simp only [r, s]
    ring_nf
  rw [sum_congr rfl hterm, ← mul_sum, hS, hxrs, hxr, hxs,
    show j + N - j = N by omega, show j + N + j = j + j + N by omega,
    qPochhammer_add (a * q / ρ1) q j N, qPochhammer_add (a * q / ρ2) q j N,
    qPochhammer_add (a * q) q (j + j) N]
  have f1 := h1
  have f2 := h2
  rw [qPochhammer_add] at f1 f2
  have f3 := haq' (j + j + N) le_rfl
  rw [qPochhammer_add] at f3
  have g1 := left_ne_zero_of_mul f1
  have g3 := left_ne_zero_of_mul f2
  have g5 := left_ne_zero_of_mul f3
  have g6 := right_ne_zero_of_mul f3
  have g7 := hqq N (by omega)
  have g2' : qPochhammer (a * q * q ^ j / ρ1) q N ≠ 0 := by
    rw [show a * q * q ^ j / ρ1 = a * q / ρ1 * q ^ j by ring]; exact right_ne_zero_of_mul f1
  have g4' : qPochhammer (a * q * q ^ j / ρ2) q N ≠ 0 := by
    rw [show a * q * q ^ j / ρ2 = a * q / ρ2 * q ^ j by ring]; exact right_ne_zero_of_mul f2
  field_simp

/-- Bailey's lemma at a fixed index `n`, with nondegeneracy hypotheses only up to `n`. -/
theorem bailey_relation {a q rho1 rho2 : ℂ} {α β : ℕ → ℂ} {n : ℕ}
    (h : ∀ k ≤ n, β k = ∑ j ∈ range (k + 1),
      α j / (qPochhammer q q (k - j) * qPochhammer (a * q) q (k + j)))
    (hρ1 : rho1 ≠ 0) (hρ2 : rho2 ≠ 0) (hqq : ∀ m ≤ n, qPochhammer q q m ≠ 0)
    (haq : qPochhammer (a * q) q (n + n) ≠ 0) (h1 : qPochhammer (a * q / rho1) q n ≠ 0)
    (h2 : qPochhammer (a * q / rho2) q n ≠ 0) :
    ∑ k ∈ range (n + 1),
        qPochhammer rho1 q k * qPochhammer rho2 q k *
            qPochhammer (a * q / (rho1 * rho2)) q (n - k) *
            (a * q / (rho1 * rho2) : ℂ) ^ k * β k /
          (qPochhammer q q (n - k) * qPochhammer (a * q / rho1) q n *
            qPochhammer (a * q / rho2) q n) =
      ∑ k ∈ range (n + 1),
        qPochhammer rho1 q k * qPochhammer rho2 q k *
            (a * q / (rho1 * rho2) : ℂ) ^ k * α k /
          (qPochhammer (a * q / rho1) q k * qPochhammer (a * q / rho2) q k) /
          (qPochhammer q q (n - k) * qPochhammer (a * q) q (n + k)) := by
  set W : ℕ → ℕ → ℂ := fun k j => qPochhammer rho1 q k * qPochhammer rho2 q k *
    qPochhammer (a * q / (rho1 * rho2)) q (n - k) * (a * q / (rho1 * rho2)) ^ k /
    (qPochhammer q q (n - k) * qPochhammer (a * q / rho1) q n * qPochhammer (a * q / rho2) q n *
      (qPochhammer q q (k - j) * qPochhammer (a * q) q (k + j))) with hW
  have hL : ∀ k ∈ range (n + 1),
      qPochhammer rho1 q k * qPochhammer rho2 q k *
          qPochhammer (a * q / (rho1 * rho2)) q (n - k) *
          (a * q / (rho1 * rho2) : ℂ) ^ k * β k /
        (qPochhammer q q (n - k) * qPochhammer (a * q / rho1) q n *
          qPochhammer (a * q / rho2) q n) =
      ∑ j ∈ Ico 0 (k + 1), α j * W k j := by
    intro k hk
    rw [h k (by simpa [Nat.lt_succ_iff] using hk), ← range_eq_Ico, mul_sum, sum_div]
    refine sum_congr rfl fun j _ => ?_
    simp only [hW]
    ring
  rw [sum_congr rfl hL, range_eq_Ico, ← sum_Ico_Ico_comm 0 (n + 1) (fun i k => α i * W k i)]
  refine sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := by simp at hi; omega
  rw [← mul_sum, hW]
  simp only
  rw [bailey_inner hρ1 hρ2 hqq haq h1 h2 hin]
  ring

/-- Bailey's lemma (AAR §12.2): a Bailey pair produces a new Bailey pair. The parameters are
nondegenerate: with `rho1 = 0` or a vanishing denominator, the totalized quotients no longer
give a Bailey pair. -/
@[dlmf 17.12.E5]
theorem bailey_lemma {a q rho1 rho2 : ℂ} {α β : ℕ → ℂ} (h : IsBaileyPair a q α β)
    (hρ1 : rho1 ≠ 0) (hρ2 : rho2 ≠ 0) (hqq : ∀ m, qPochhammer q q m ≠ 0)
    (haq : ∀ m, qPochhammer (a * q) q m ≠ 0) (h1 : ∀ m, qPochhammer (a * q / rho1) q m ≠ 0)
    (h2 : ∀ m, qPochhammer (a * q / rho2) q m ≠ 0) :
    IsBaileyPair a q
      (fun n =>
        qPochhammer rho1 q n * qPochhammer rho2 q n *
            (a * q / (rho1 * rho2) : ℂ) ^ n * α n /
          (qPochhammer (a * q / rho1) q n * qPochhammer (a * q / rho2) q n))
      (fun n =>
        ∑ k ∈ Finset.range (n + 1),
          qPochhammer rho1 q k * qPochhammer rho2 q k *
              qPochhammer (a * q / (rho1 * rho2)) q (n - k) *
              (a * q / (rho1 * rho2) : ℂ) ^ k * β k /
            (qPochhammer q q (n - k) * qPochhammer (a * q / rho1) q n *
              qPochhammer (a * q / rho2) q n)) := by
  intro n
  exact bailey_relation (fun k _ => h k) hρ1 hρ2 (fun m _ => hqq m) (haq (n + n)) (h1 n) (h2 n)

/-! ### Helpers for Watson's transformation -/

private lemma choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

/-- `(qt;q)_k (-qt;q)_k (1-a) = (t;q)_k (-t;q)_k (1-aq^{2k})` when `t² = a`: the
very-well-poised factor of `₈φ₇` for either square root of `a`. -/
theorem qPochhammer_sqrt_factor {a q t : ℂ} (ht : t ^ 2 = a) (k : ℕ) :
    qPochhammer (q * t) q k * qPochhammer (-q * t) q k * (1 - a) =
      qPochhammer t q k * qPochhammer (-t) q k * (1 - a * q ^ (2 * k)) := by
  subst ht
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [qPochhammer_succ]
    linear_combination (1 - q * t * q ^ k) * (1 - -q * t * q ^ k) * ih

/-- Reversal: `(xq^m;q)_k = (-x)^k q^{mk + k(k-1)/2} (y;q)_k` when `x y q^{m+k} = q`. -/
theorem qPochhammer_mul_pow_eq_reverse {x y q : ℂ} (hq : q ≠ 0) (k : ℕ) :
    ∀ m : ℕ, x * y * q ^ (m + k) = q →
      qPochhammer (x * q ^ m) q k = (-x) ^ k * q ^ (m * k + k.choose 2) * qPochhammer y q k := by
  induction k with
  | zero => intro m _; simp
  | succ k ih =>
    intro m hm
    have h1 : x * y * q ^ (m + k) = 1 := by
      rw [show m + (k + 1) = m + k + 1 by omega, pow_succ] at hm
      apply mul_right_cancel₀ hq
      linear_combination hm
    rw [qPochhammer_succ', show x * q ^ m * q = x * q ^ (m + 1) by ring,
      ih (m + 1) (by rw [show m + 1 + k = m + (k + 1) by omega]; exact hm),
      qPochhammer_succ, choose_two_succ,
      show m * (k + 1) + (k.choose 2 + k) = (m + 1) * k + k.choose 2 + m by ring, pow_add,
      pow_succ (-x)]
    linear_combination (-x) ^ k * q ^ ((m + 1) * k + k.choose 2) * qPochhammer y q k * (-1) * h1

/-- The numerator of the unit Bailey pair, divided by `1 - a`: `1` at `k = 0`, and
`(aq;q)_{k-1} (1 - aq^{2k})` for `k ≥ 1`. -/
def unitD (a q : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => qPochhammer (a * q) q k * (1 - a * q ^ (2 * (k + 1)))

/-- The unit Bailey pair `α_k = (a;q)_k (1 - aq^{2k}) (-1)^k q^{k(k-1)/2} / ((q;q)_k (1 - a))`,
written without the division by `1 - a`. -/
def unitAlpha (a q : ℂ) (k : ℕ) : ℂ :=
  unitD a q k * (-1) ^ k * q ^ k.choose 2 / qPochhammer q q k

/-- Partial sums of the unit-pair polynomial identity. -/
private lemma unit_partial (a q : ℂ) (n : ℕ) :
    ∀ m ≤ n + 1, ∑ k ∈ range (m + 1), qBinom q (n + 1) k * (-1) ^ k * q ^ k.choose 2 *
        unitD a q k * qPochhammer (a * q * q ^ (n + 1 + k)) q (n + 1 - k) =
      (-1) ^ m * q ^ (m + 1).choose 2 * qBinom q n m * qPochhammer (a * q) q m *
        qPochhammer (a * q * q ^ (n + 1 + m)) q (n + 1 - m) := by
  intro m hm
  induction m with
  | zero => simp [unitD]
  | succ m ih =>
    rw [sum_range_succ, ih (by omega)]
    obtain ⟨d, rfl⟩ : ∃ d, n = m + d := ⟨n - m, by omega⟩
    have hP1 := qBinom_succ_succ q (m + d) m
    have hP2 := qBinom_succ_succ' q (m + d) m
    rw [show m + d - m = d by omega] at hP2
    rw [show m + d + 1 - m = d + 1 by omega, show m + d + 1 - (m + 1) = d by omega,
      qPochhammer_succ' (a * q * q ^ (m + d + 1 + m)) q d, qPochhammer_succ (a * q) q m,
      show a * q * q ^ (m + d + 1 + m) * q = a * q * q ^ (m + d + 1 + (m + 1)) by ring,
      choose_two_succ (m + 1), choose_two_succ m]
    simp only [unitD]
    linear_combination
      (-1) ^ m * q ^ (m.choose 2 + m) * qPochhammer (a * q) q m *
        qPochhammer (a * q * q ^ (m + d + 1 + (m + 1))) q d *
        (-(hP1) + a * q ^ (2 * (m + 1)) * hP2)

/-- The unit Bailey pair identity in polynomial form: for `n ≥ 1`,
`∑_k [n k]_q (-1)^k q^{k(k-1)/2} D_k (aq^{n+k+1};q)_{n-k} = 0`. -/
theorem unit_poly (a q : ℂ) (n : ℕ) :
    ∑ k ∈ range (n + 1 + 1), qBinom q (n + 1) k * (-1) ^ k * q ^ k.choose 2 *
        unitD a q k * qPochhammer (a * q * q ^ (n + 1 + k)) q (n + 1 - k) = 0 := by
  rw [unit_partial a q n (n + 1) le_rfl, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
  ring

/-- The unit Bailey pair relative to `a`: `δ_{n,0} = ∑_k α_k / ((q;q)_{n-k} (aq;q)_{n+k})`. -/
theorem unit_pair (a q : ℂ) (n : ℕ) (hqq : ∀ m ≤ n, qPochhammer q q m ≠ 0)
    (haq : qPochhammer (a * q) q (n + n) ≠ 0) :
    (if n = 0 then 1 else 0) = ∑ k ∈ range (n + 1),
      unitAlpha a q k / (qPochhammer q q (n - k) * qPochhammer (a * q) q (n + k)) := by
  rcases n with _ | n
  · simp [unitAlpha, unitD]
  simp only [Nat.add_one_ne_zero, ↓reduceIte]
  rw [eq_comm]
  have hne : qPochhammer q q (n + 1) * qPochhammer (a * q) q (n + 1 + (n + 1)) ≠ 0 :=
    mul_ne_zero (hqq _ le_rfl) haq
  rw [← mul_eq_zero_iff_right hne, sum_mul, ← unit_poly a q n]
  refine sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n + 1 := by simpa [Nat.lt_succ_iff] using hk
  have hB := qBinom_mul_qPochhammer q k (n + 1 - k)
  have hS := qPochhammer_add (a * q) q (n + 1 + k) (n + 1 - k)
  rw [Nat.add_sub_cancel' hkn] at hB
  rw [show n + 1 + k + (n + 1 - k) = n + 1 + (n + 1) by omega] at hS
  have h1 := hqq k hkn
  have h2 := hqq (n + 1 - k) (by omega)
  have h3 : qPochhammer (a * q) q (n + 1 + k) ≠ 0 :=
    qPochhammer_ne_zero_of_le haq (by omega)
  rw [← hB, hS, unitAlpha]
  field_simp

private lemma two_choose_add (k : ℕ) : k.choose 2 + k.choose 2 + k = k * k := by
  induction k with
  | zero => simp
  | succ k ih => rw [choose_two_succ]; nlinarith

theorem qPochhammer_mul_one_sub_pow (a q : ℂ) (k : ℕ) :
    qPochhammer a q k * (1 - a * q ^ (2 * k)) = (1 - a) * unitD a q k := by
  rcases k with _ | k
  · simp [unitD]
  · simp only [unitD, qPochhammer_succ']
    ring

theorem qPochhammer_ne_zero_of_forall {x q : ℂ} {n : ℕ} (h : ∀ k ≤ n, x * q ^ k ≠ 1) :
    ∀ m ≤ n + 1, qPochhammer x q m ≠ 0 := by
  intro m hm
  rw [qPochhammer_eq_prod, prod_ne_zero_iff]
  intro i hi
  exact sub_ne_zero.mpr (h i (by simp at hi; omega)).symm

private lemma pow_aux (q : ℂ) {n k : ℕ} (hkn : k ≤ n) :
    (q ^ n) ^ k = q ^ k.choose 2 * q ^ k.choose 2 * q ^ k * q ^ ((n - k) * k) := by
  rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add, two_choose_add]
  congr 1
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hkn
  rw [Nat.add_sub_cancel_left]; ring

/-- The field algebra behind the `₈φ₇` side of Watson's transformation. -/
private lemma watson_alg8 (U Pb Pc Pd Pe Pinv PB PC PD PE Paqn Pqk Pqnk Paq x1 x2 q : ℂ)
    {n k : ℕ} (hkn : k ≤ n) (h1 : PB ≠ 0) (h2 : PC ≠ 0) (h3 : PD ≠ 0) (h4 : PE ≠ 0)
    (h5 : Paqn ≠ 0) (h6 : Pqk ≠ 0) (h7 : Pqnk ≠ 0) (h8 : Paq ≠ 0) :
    U * (Pb * Pc * Pd * Pe * Pinv) / (PB * PC * PD * PE * Paqn * Pqk) * (x1 * x2 * q ^ n) ^ k =
      Pqnk * ((-q) ^ k * q ^ ((n - k) * k + k.choose 2) * Pinv) * Paq *
        (Pd * Pe * x2 ^ k * (Pb * Pc * x1 ^ k * (U * (-1) ^ k * q ^ k.choose 2 / Pqk) / (PB * PC)) /
          (PD * PE) / (Pqnk * (Paq * Paqn))) := by
  have hs : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [mul_pow, mul_pow, pow_aux q hkn, neg_pow, pow_add]
  field_simp
  linear_combination (-(U * Pb * Pc * Pd * Pe * Pinv * x1 ^ k * x2 ^ k * q ^ k.choose 2 *
    q ^ k.choose 2 * q ^ k * q ^ ((n - k) * k))) * hs

/-- The field algebra behind the `₄φ₃` side of Watson's transformation. -/
private lemma watson_alg4 (Paq Px2nk PY PD PE Pinv Pd Pe Px1 PB PC Pqk Pqnk x2 q : ℂ) (E k : ℕ)
    (h1 : PD ≠ 0) (h2 : PE ≠ 0) (h3 : PB ≠ 0) (h4 : PC ≠ 0) (h5 : PY ≠ 0) (h6 : Pqk ≠ 0)
    (h7 : Pqnk ≠ 0) :
    Paq * (Px2nk * ((-x2) ^ k * q ^ E * PY)) / (PD * PE) *
        (Pinv * Pd * Pe * Px1 / (PB * PC * PY * Pqk) * q ^ k) =
      Pqnk * ((-q) ^ k * q ^ E * Pinv) * Paq *
        (Pd * Pe * Px2nk * x2 ^ k * (Px1 / (Pqk * PB * PC)) / (Pqnk * PD * PE)) := by
  rw [neg_pow, neg_pow]
  field_simp
  ring

/-- The rational form of the `₈φ₇` summand in Watson's transformation, with the very-well-poised
factor written as `unitD`. -/
def watsonR8 (a b c d e q : ℂ) (n k : ℕ) : ℂ :=
  unitD a q k * (qPochhammer b q k * qPochhammer c q k * qPochhammer d q k *
      qPochhammer e q k * qPochhammer (q⁻¹ ^ n) q k) /
    (qPochhammer (a * q / b) q k * qPochhammer (a * q / c) q k * qPochhammer (a * q / d) q k *
      qPochhammer (a * q / e) q k * qPochhammer (a * q * q ^ n) q k * qPochhammer q q k) *
    (a ^ 2 * q ^ 2 * q ^ n / (b * c * d * e)) ^ k

/-- The summand of the balanced `₄φ₃` in Watson's transformation. -/
def watsonR4 (a b c d e q : ℂ) (n k : ℕ) : ℂ :=
  qPochhammer (q⁻¹ ^ n) q k * qPochhammer d q k * qPochhammer e q k *
      qPochhammer (a * q / (b * c)) q k /
    (qPochhammer (a * q / b) q k * qPochhammer (a * q / c) q k *
      qPochhammer (d * e * q⁻¹ ^ n / a) q k * qPochhammer q q k) * q ^ k

/-- Watson's transformation in rational form, when `(aq;q)_{2n} ≠ 0`: two applications of
Bailey's lemma to the unit Bailey pair, first with `(b, c)` and then with `(d, e)`. -/
theorem watsonR_of_ne {a b c d e q : ℂ} (n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hq : q ≠ 0) (hqq : ∀ m ≤ n, qPochhammer q q m ≠ 0)
    (haq : qPochhammer (a * q) q (n + n) ≠ 0)
    (hB : qPochhammer (a * q / b) q n ≠ 0) (hC : qPochhammer (a * q / c) q n ≠ 0)
    (hD : qPochhammer (a * q / d) q n ≠ 0) (hE : qPochhammer (a * q / e) q n ≠ 0)
    (hY : qPochhammer (d * e * q⁻¹ ^ n / a) q n ≠ 0) :
    ∑ k ∈ range (n + 1), watsonR8 a b c d e q n k =
      qPochhammer (a * q) q n * qPochhammer (a * q / (d * e)) q n /
          (qPochhammer (a * q / d) q n * qPochhammer (a * q / e) q n) *
        ∑ k ∈ range (n + 1), watsonR4 a b c d e q n k := by
  set x1 := a * q / (b * c) with hx1
  set x2 := a * q / (d * e) with hx2
  set β0 : ℕ → ℂ := fun i => if i = 0 then 1 else 0 with hβ0
  set α1 : ℕ → ℂ := fun j => qPochhammer b q j * qPochhammer c q j * x1 ^ j * unitAlpha a q j /
    (qPochhammer (a * q / b) q j * qPochhammer (a * q / c) q j) with hα1
  set β1 : ℕ → ℂ := fun k => ∑ i ∈ range (k + 1), qPochhammer b q i * qPochhammer c q i *
    qPochhammer x1 q (k - i) * x1 ^ i * β0 i /
      (qPochhammer q q (k - i) * qPochhammer (a * q / b) q k * qPochhammer (a * q / c) q k)
    with hβ1
  have haq' : ∀ m ≤ n + n, qPochhammer (a * q) q m ≠ 0 :=
    fun m hm => qPochhammer_ne_zero_of_le haq hm
  -- the first Bailey step, at every `k ≤ n`
  have step1 : ∀ k ≤ n, β1 k = ∑ j ∈ range (k + 1),
      α1 j / (qPochhammer q q (k - j) * qPochhammer (a * q) q (k + j)) := by
    intro k hk
    exact bailey_relation (α := unitAlpha a q) (β := β0)
      (fun i hi => unit_pair a q i (fun m hm => hqq m (by omega)) (haq' _ (by omega)))
      hb hc (fun m hm => hqq m (by omega)) (haq' _ (by omega))
      (qPochhammer_ne_zero_of_le hB hk) (qPochhammer_ne_zero_of_le hC hk)
  -- the second Bailey step, at `n`
  have step2 := bailey_relation (n := n) (α := α1) (β := β1) step1 hd he hqq haq hD hE
  -- the closed form of `β1`
  have hβ1c : ∀ k, β1 k = qPochhammer x1 q k /
      (qPochhammer q q k * qPochhammer (a * q / b) q k * qPochhammer (a * q / c) q k) := by
    intro k
    simp only [hβ1]
    rw [sum_eq_single 0 (fun i _ hi => by simp [hβ0, hi]) (fun h => by simp at h)]
    simp [hβ0]
  have hqn : qPochhammer q q n ≠ 0 := hqq n le_rfl
  have haqn : qPochhammer (a * q) q n ≠ 0 := haq' n (by omega)
  -- the `₈φ₇` side
  have h8 : ∀ k ∈ range (n + 1), watsonR8 a b c d e q n k =
      qPochhammer q q n * qPochhammer (a * q) q n *
        (qPochhammer d q k * qPochhammer e q k * x2 ^ k * α1 k /
          (qPochhammer (a * q / d) q k * qPochhammer (a * q / e) q k) /
          (qPochhammer q q (n - k) * qPochhammer (a * q) q (n + k))) := by
    intro k hk
    have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    have hsplit := qPochhammer_add q q (n - k) k
    rw [Nat.sub_add_cancel hkn] at hsplit
    have hrev := qPochhammer_mul_pow_eq_reverse (x := q) (y := q⁻¹ ^ n) hq k (n - k)
      (by rw [Nat.sub_add_cancel hkn, inv_pow]; field_simp)
    have haqk := qPochhammer_add (a * q) q n k
    have n1 := hqq k hkn
    have n2 := hqq (n - k) (by omega)
    have n3 := qPochhammer_ne_zero_of_le hB hkn
    have n4 := qPochhammer_ne_zero_of_le hC hkn
    have n5 := qPochhammer_ne_zero_of_le hD hkn
    have n6 := qPochhammer_ne_zero_of_le hE hkn
    have n7 : qPochhammer (a * q * q ^ n) q k ≠ 0 := by
      have := haq' (n + k) (by omega)
      rw [haqk] at this
      exact right_ne_zero_of_mul this
    simp only [watsonR8, hα1, unitAlpha]
    rw [hsplit, hrev, haqk,
      show a ^ 2 * q ^ 2 * q ^ n / (b * c * d * e) = x1 * x2 * q ^ n by
        simp only [hx1, hx2]; field_simp]
    exact watson_alg8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hkn n3 n4 n5 n6 n7 n1 n2 haqn
  -- the `₄φ₃` side
  have h4 : ∀ k ∈ range (n + 1),
      qPochhammer (a * q) q n * qPochhammer x2 q n /
          (qPochhammer (a * q / d) q n * qPochhammer (a * q / e) q n) *
        watsonR4 a b c d e q n k =
      qPochhammer q q n * qPochhammer (a * q) q n *
        (qPochhammer d q k * qPochhammer e q k * qPochhammer x2 q (n - k) * x2 ^ k * β1 k /
          (qPochhammer q q (n - k) * qPochhammer (a * q / d) q n *
            qPochhammer (a * q / e) q n)) := by
    intro k hk
    have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
    have hsplit := qPochhammer_add q q (n - k) k
    rw [Nat.sub_add_cancel hkn] at hsplit
    have hrev := qPochhammer_mul_pow_eq_reverse (x := q) (y := q⁻¹ ^ n) hq k (n - k)
      (by rw [Nat.sub_add_cancel hkn, inv_pow]; field_simp)
    have hsplit2 := qPochhammer_add x2 q (n - k) k
    rw [Nat.sub_add_cancel hkn] at hsplit2
    have hrev2 := qPochhammer_mul_pow_eq_reverse (x := x2) (y := d * e * q⁻¹ ^ n / a) hq k
      (n - k) (by rw [Nat.sub_add_cancel hkn, inv_pow, hx2]; field_simp)
    have n1 := hqq k hkn
    have n2 := hqq (n - k) (by omega)
    have n3 := qPochhammer_ne_zero_of_le hB hkn
    have n4 := qPochhammer_ne_zero_of_le hC hkn
    have n8 := qPochhammer_ne_zero_of_le hY hkn
    simp only [watsonR4, hβ1c]
    rw [hsplit, hrev, hsplit2, hrev2]
    exact watson_alg4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD hE n3 n4 n8 n1 n2
  rw [sum_congr rfl h8, ← mul_sum, ← step2, mul_sum, mul_sum]
  exact (sum_congr rfl h4).symm

theorem continuous_qPochhammer_comp {f : ℂ → ℂ} (hf : Continuous f) (q : ℂ) (k : ℕ) :
    Continuous fun t => qPochhammer (f t) q k := by
  simp only [qPochhammer_eq_prod]
  exact continuous_finsetProd _ fun i _ => continuous_const.sub (hf.mul continuous_const)

theorem continuous_unitD (q : ℂ) (k : ℕ) : Continuous fun t => unitD t q k := by
  rcases k with _ | k
  · simp only [unitD]; exact continuous_const
  · simp only [unitD]
    exact (continuous_qPochhammer_comp (continuous_id.mul continuous_const) q k).mul
      (continuous_const.sub (continuous_id.mul continuous_const))

private lemma eventually_ne_punctured (a c : ℂ) : ∀ᶠ t in 𝓝[≠] a, t ≠ c := by
  by_cases h : a = c
  · subst h; exact eventually_nhdsWithin_iff.mpr (Filter.Eventually.of_forall fun t ht => ht)
  · exact (continuousAt_id.eventually_ne h).filter_mono nhdsWithin_le_nhds

private lemma eventually_qPochhammer_ne_zero (a q : ℂ) (hq : q ≠ 0) (m : ℕ) :
    ∀ᶠ t in 𝓝[≠] a, qPochhammer (t * q) q m ≠ 0 := by
  have h : ∀ᶠ t in 𝓝[≠] a, ∀ i ∈ range m, t ≠ (q * q ^ i)⁻¹ :=
    (Filter.eventually_all_finset _).mpr fun i _ => eventually_ne_punctured a _
  filter_upwards [h] with t ht
  rw [qPochhammer_eq_prod, prod_ne_zero_iff]
  intro i hi
  have hqi : q * q ^ i ≠ 0 := mul_ne_zero hq (pow_ne_zero _ hq)
  intro h0
  exact ht i hi (eq_inv_of_mul_eq_one_left (by linear_combination -h0))

/-- Watson's transformation in rational form, for all `a` with the natural denominators
nonzero; the degenerate values of `a` with `(aq;q)_{2n} = 0` follow by continuity in `a`. -/
theorem watsonR {a b c d e q : ℂ} (n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hq : q ≠ 0) (hqq : ∀ m ≤ n, qPochhammer q q m ≠ 0)
    (hB : qPochhammer (a * q / b) q n ≠ 0) (hC : qPochhammer (a * q / c) q n ≠ 0)
    (hD : qPochhammer (a * q / d) q n ≠ 0) (hE : qPochhammer (a * q / e) q n ≠ 0)
    (hY : qPochhammer (d * e * q⁻¹ ^ n / a) q n ≠ 0)
    (hN : qPochhammer (a * q * q ^ n) q n ≠ 0) :
    ∑ k ∈ range (n + 1), watsonR8 a b c d e q n k =
      qPochhammer (a * q) q n * qPochhammer (a * q / (d * e)) q n /
          (qPochhammer (a * q / d) q n * qPochhammer (a * q / e) q n) *
        ∑ k ∈ range (n + 1), watsonR4 a b c d e q n k := by
  set F : ℂ → ℂ := fun t => ∑ k ∈ range (n + 1), watsonR8 t b c d e q n k -
    qPochhammer (t * q) q n * qPochhammer (t * q / (d * e)) q n /
        (qPochhammer (t * q / d) q n * qPochhammer (t * q / e) q n) *
      ∑ k ∈ range (n + 1), watsonR4 t b c d e q n k with hF
  suffices F a = 0 by simpa [hF, sub_eq_zero] using this
  have cP : ∀ (g : ℂ → ℂ), Continuous g → ∀ k, Continuous fun t => qPochhammer (g t) q k :=
    fun g hg k => continuous_qPochhammer_comp hg q k
  -- continuity of `F` at `a`
  have hcont : ContinuousAt F a := by
    have hBk : ∀ k ≤ n, qPochhammer (a * q / b) q k ≠ 0 :=
      fun k hk => qPochhammer_ne_zero_of_le hB hk
    have hCk : ∀ k ≤ n, qPochhammer (a * q / c) q k ≠ 0 :=
      fun k hk => qPochhammer_ne_zero_of_le hC hk
    have hDk : ∀ k ≤ n, qPochhammer (a * q / d) q k ≠ 0 :=
      fun k hk => qPochhammer_ne_zero_of_le hD hk
    have hEk : ∀ k ≤ n, qPochhammer (a * q / e) q k ≠ 0 :=
      fun k hk => qPochhammer_ne_zero_of_le hE hk
    have hYk : ∀ k ≤ n, qPochhammer (d * e * q⁻¹ ^ n / a) q k ≠ 0 :=
      fun k hk => qPochhammer_ne_zero_of_le hY hk
    have hNk : ∀ k ≤ n, qPochhammer (a * q * q ^ n) q k ≠ 0 :=
      fun k hk => qPochhammer_ne_zero_of_le hN hk
    apply ContinuousAt.sub
    · refine tendsto_finsetSum _ fun k hk => ?_
      have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
      show ContinuousAt (fun t => watsonR8 t b c d e q n k) a
      simp only [watsonR8]
      refine ContinuousAt.mul (ContinuousAt.div ?_ ?_ ?_) ?_
      · exact ((continuous_unitD q k).mul continuous_const).continuousAt
      · exact ((((((cP _ ((continuous_id.mul continuous_const).div_const b) k).mul
          (cP _ ((continuous_id.mul continuous_const).div_const c) k)).mul
          (cP _ ((continuous_id.mul continuous_const).div_const d) k)).mul
          (cP _ ((continuous_id.mul continuous_const).div_const e) k)).mul
          (cP _ ((continuous_id.mul continuous_const).mul continuous_const) k)).mul
          continuous_const).continuousAt
      · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (hBk k hkn)
          (hCk k hkn)) (hDk k hkn)) (hEk k hkn)) (hNk k hkn)) (hqq k hkn)
      · exact ((((continuous_id.pow 2).mul continuous_const).mul continuous_const).div_const
          _).pow k |>.continuousAt
    · refine ContinuousAt.mul (ContinuousAt.div ?_ ?_ (mul_ne_zero hD hE)) ?_
      · exact ((cP _ (continuous_id.mul continuous_const) n).mul
          (cP _ ((continuous_id.mul continuous_const).div_const _) n)).continuousAt
      · exact ((cP _ ((continuous_id.mul continuous_const).div_const d) n).mul
          (cP _ ((continuous_id.mul continuous_const).div_const e) n)).continuousAt
      · refine tendsto_finsetSum _ fun k hk => ?_
        have hkn : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
        show ContinuousAt (fun t => watsonR4 t b c d e q n k) a
        simp only [watsonR4]
        refine ContinuousAt.mul (ContinuousAt.div ?_ ?_ ?_) continuousAt_const
        · exact (continuous_const.mul
            (cP _ ((continuous_id.mul continuous_const).div_const _) k)).continuousAt
        · have hg : ContinuousAt (fun t : ℂ => d * e * q⁻¹ ^ n / t) a :=
            continuousAt_const.div continuousAt_id ha
          have hYc : ContinuousAt (fun t : ℂ => qPochhammer (d * e * q⁻¹ ^ n / t) q k) a := by
            simp only [qPochhammer_eq_prod]
            exact tendsto_finsetProd _ fun i _ =>
              continuousAt_const.sub (hg.mul continuousAt_const)
          exact ((((cP _ ((continuous_id.mul continuous_const).div_const b) k).continuousAt.mul
            (cP _ ((continuous_id.mul continuous_const).div_const c) k).continuousAt).mul
            hYc).mul continuousAt_const)
        · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hBk k hkn) (hCk k hkn)) (hYk k hkn))
            (hqq k hkn)
  -- `F` vanishes on a punctured neighbourhood of `a`
  have hev : ∀ᶠ t in 𝓝[≠] a, F t = 0 := by
    have c1 : ContinuousAt (fun t : ℂ => qPochhammer (t * q / b) q n) a :=
      (cP _ ((continuous_id.mul continuous_const).div_const b) n).continuousAt
    have c2 : ContinuousAt (fun t : ℂ => qPochhammer (t * q / c) q n) a :=
      (cP _ ((continuous_id.mul continuous_const).div_const c) n).continuousAt
    have c3 : ContinuousAt (fun t : ℂ => qPochhammer (t * q / d) q n) a :=
      (cP _ ((continuous_id.mul continuous_const).div_const d) n).continuousAt
    have c4 : ContinuousAt (fun t : ℂ => qPochhammer (t * q / e) q n) a :=
      (cP _ ((continuous_id.mul continuous_const).div_const e) n).continuousAt
    have c5 : ContinuousAt (fun t : ℂ => qPochhammer (d * e * q⁻¹ ^ n / t) q n) a := by
      have hg : ContinuousAt (fun t : ℂ => d * e * q⁻¹ ^ n / t) a :=
        continuousAt_const.div continuousAt_id ha
      simp only [qPochhammer_eq_prod]
      exact tendsto_finsetProd _ fun i _ => continuousAt_const.sub (hg.mul continuousAt_const)
    filter_upwards [(c1.eventually_ne hB).filter_mono nhdsWithin_le_nhds,
      (c2.eventually_ne hC).filter_mono nhdsWithin_le_nhds,
      (c3.eventually_ne hD).filter_mono nhdsWithin_le_nhds,
      (c4.eventually_ne hE).filter_mono nhdsWithin_le_nhds,
      (c5.eventually_ne hY).filter_mono nhdsWithin_le_nhds,
      eventually_ne_punctured a 0, eventually_qPochhammer_ne_zero a q hq (n + n)]
      with t h1 h2 h3 h4 h5 h6 h7
    simp only [hF, sub_eq_zero]
    exact watsonR_of_ne n h6 hb hc hd he hq hqq h7 h1 h2 h3 h4 h5
  have h1 : Filter.Tendsto F (𝓝[≠] a) (𝓝 (F a)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto F (𝓝[≠] a) (𝓝 0) :=
    tendsto_const_nhds.congr' (hev.mono fun t ht => ht.symm)
  exact tendsto_nhds_unique h1 h2

private lemma qPochhammer_recip_pow_zero {q : ℂ} (hq : q ≠ 0) {n k : ℕ} (hk : n < k) :
    qPochhammer (q⁻¹ ^ n) q k = 0 := by
  rw [qPochhammer_eq_prod]
  exact prod_eq_zero (mem_range.mpr hk) (by rw [inv_pow]; field_simp; ring)

/-- Watson's transformation of a terminating very-well-poised `₈φ₇` into a balanced `₄φ₃`
(AAR §12.3), with `f = q⁻ⁿ`. The listed denominator parameters must not produce vanishing
factors in the finite sums. -/
@[dlmf 17.9.E15]
theorem watson_transformation {a b c d e q : ℂ} (n : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (he : e ≠ 0) (hq : q ≠ 0)
    (hden : ∀ x ∈ [a ^ (1 / 2 : ℂ), -a ^ (1 / 2 : ℂ), a * q / b, a * q / c, a * q / d,
      a * q / e, a * q * q ^ n, d * e * q⁻¹ ^ n / a, q], ∀ k : ℕ, k ≤ n → x * q ^ k ≠ 1) :
    basicHG [a, q * a ^ (1 / 2 : ℂ), -q * a ^ (1 / 2 : ℂ), b, c, d, e, q⁻¹ ^ n]
        [a ^ (1 / 2 : ℂ), -a ^ (1 / 2 : ℂ), a * q / b, a * q / c, a * q / d, a * q / e,
          a * q * q ^ n] q
        (a ^ 2 * q ^ 2 * q ^ n / (b * c * d * e)) =
      qPochhammer (a * q) q n * qPochhammer (a * q / (d * e)) q n /
          (qPochhammer (a * q / d) q n * qPochhammer (a * q / e) q n) *
        basicHG [q⁻¹ ^ n, d, e, a * q / (b * c)]
          [a * q / b, a * q / c, d * e * q⁻¹ ^ n / a] q q := by
  have H : ∀ x ∈ [a ^ (1 / 2 : ℂ), -a ^ (1 / 2 : ℂ), a * q / b, a * q / c, a * q / d,
      a * q / e, a * q * q ^ n, d * e * q⁻¹ ^ n / a, q], ∀ m ≤ n + 1, qPochhammer x q m ≠ 0 :=
    fun x hx => qPochhammer_ne_zero_of_forall (hden x hx)
  set t := a ^ (1 / 2 : ℂ) with htdef
  have ht : t ^ 2 = a := by rw [htdef, one_div]; exact Complex.cpow_ofNat_inv_pow a 2
  have h1a : 1 - a ≠ 0 := by
    intro h
    have hp := hden t (by simp) 0 (Nat.zero_le _)
    have hm := hden (-t) (by simp) 0 (Nat.zero_le _)
    simp only [pow_zero, mul_one] at hp hm
    have : (t - 1) * (t + 1) = 0 := by linear_combination ht - h
    rcases mul_eq_zero.mp this with h' | h'
    · exact hp (by linear_combination h')
    · exact hm (by linear_combination -h')
  have Ht := H t (by simp)
  have Hnt := H (-t) (by simp)
  have HB := H (a * q / b) (by simp)
  have HC := H (a * q / c) (by simp)
  have HD := H (a * q / d) (by simp)
  have HE := H (a * q / e) (by simp)
  have HN := H (a * q * q ^ n) (by simp)
  have HY := H (d * e * q⁻¹ ^ n / a) (by simp)
  have HQ := H q (by simp)
  have hW := watsonR n ha hb hc hd he hq (fun m hm => HQ m (by omega)) (HB n (by omega))
    (HC n (by omega)) (HD n (by omega)) (HE n (by omega)) (HY n (by omega)) (HN n (by omega))
  have hzero : ∀ k, n < k → qPochhammer (q⁻¹ ^ n) q k = 0 :=
    fun k hk => qPochhammer_recip_pow_zero hq hk
  unfold basicHG
  rw [tsum_eq_sum (s := range (n + 1)), tsum_eq_sum (s := range (n + 1))]
  rotate_left
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      hzero k (by simpa using hk)]
    simp
  · intro k hk
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      hzero k (by simpa using hk)]
    simp
  have hL8 : ∀ k ∈ range (n + 1),
      (List.map (fun ai => qPochhammer ai q k) [a, q * t, -q * t, b, c, d, e, q⁻¹ ^ n]).prod /
          ((List.map (fun bi => qPochhammer bi q k)
            [t, -t, a * q / b, a * q / c, a * q / d, a * q / e, a * q * q ^ n]).prod *
            qPochhammer q q k) * (a ^ 2 * q ^ 2 * q ^ n / (b * c * d * e)) ^ k =
        watsonR8 a b c d e q n k := by
    intro k hk
    have hkn : k ≤ n + 1 := by simp at hk; omega
    have key : qPochhammer a q k * (qPochhammer (q * t) q k * qPochhammer (-q * t) q k) =
        unitD a q k * (qPochhammer t q k * qPochhammer (-t) q k) := by
      have s1 := qPochhammer_sqrt_factor (q := q) ht k
      have s2 := qPochhammer_mul_one_sub_pow a q k
      apply mul_left_cancel₀ h1a
      linear_combination qPochhammer a q k * s1 + qPochhammer t q k * qPochhammer (-t) q k * s2
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, watsonR8]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_eq_div_iff (mul_ne_zero (mul_ne_zero (Ht k hkn) (mul_ne_zero (Hnt k hkn)
        (mul_ne_zero (HB k hkn) (mul_ne_zero (HC k hkn) (mul_ne_zero (HD k hkn)
          (mul_ne_zero (HE k hkn) (HN k hkn))))))) (HQ k hkn))
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (HB k hkn)
          (HC k hkn)) (HD k hkn)) (HE k hkn)) (HN k hkn)) (HQ k hkn))]
    linear_combination (qPochhammer b q k * qPochhammer c q k * qPochhammer d q k *
      qPochhammer e q k * qPochhammer (q⁻¹ ^ n) q k *
      (a ^ 2 * q ^ 2 * q ^ n / (b * c * d * e)) ^ k *
      (qPochhammer (a * q / b) q k * qPochhammer (a * q / c) q k * qPochhammer (a * q / d) q k *
        qPochhammer (a * q / e) q k * qPochhammer (a * q * q ^ n) q k * qPochhammer q q k)) * key
  have hR4 : ∀ k ∈ range (n + 1),
      (List.map (fun ai => qPochhammer ai q k) [q⁻¹ ^ n, d, e, a * q / (b * c)]).prod /
          ((List.map (fun bi => qPochhammer bi q k)
            [a * q / b, a * q / c, d * e * q⁻¹ ^ n / a]).prod * qPochhammer q q k) * q ^ k =
        watsonR4 a b c d e q n k := by
    intro k _
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, watsonR4]
    ring
  rw [sum_congr rfl hL8, sum_congr rfl hR4]
  exact hW

/-! ### Letting `n → ∞` -/

private lemma exists_norm_le_of_tendsto {u : ℕ → ℂ} {L : ℂ} (hu : Tendsto u atTop (𝓝 L)) :
    ∃ C, ∀ n, ‖u n‖ ≤ C := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto u hu)
  exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩

private lemma qPochhammer_ne_zero_of_norm {x q : ℂ} (hx : ‖x‖ < 1) (hq : ‖q‖ < 1) (m : ℕ) :
    qPochhammer x q m ≠ 0 := by
  rw [qPochhammer_eq_prod, prod_ne_zero_iff]
  exact fun i _ => one_sub_mul_pow_ne_zero_of_norm hx hq i

/-- Tannery's theorem for the finite sums of the Bailey relation. -/
private lemma tendsto_sum_range_mul {u : ℕ → ℂ} {v : ℕ → ℕ → ℂ} {L : ℂ} {C : ℝ}
    (hu : Summable fun k => ‖u k‖) (hv : ∀ k, Tendsto (fun N => v N k) atTop (𝓝 L))
    (hC : ∀ N k, ‖v N k‖ ≤ C) :
    Tendsto (fun N => ∑ k ∈ range (N + 1), u k * v N k) atTop (𝓝 ((∑' k, u k) * L)) := by
  have heq : ∀ N, ∑ k ∈ range (N + 1), u k * v N k =
      ∑' k, (if k ≤ N then u k * v N k else 0) := by
    intro N
    rw [tsum_eq_sum (s := range (N + 1))]
    · exact sum_congr rfl fun k hk => by
        simp [show k ≤ N by simpa [Nat.lt_succ_iff] using hk]
    · intro k hk
      simp [show ¬k ≤ N by simpa [Nat.lt_succ_iff] using hk]
  simp only [heq]
  rw [← tsum_mul_right]
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => ‖u k‖ * C) (hu.mul_right C)
    (fun k => ?_) (Eventually.of_forall fun N k => ?_)
  · refine ((hv k).const_mul (u k)).congr' ?_
    filter_upwards [eventually_ge_atTop k] with N hN
    simp [hN]
  · split_ifs
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC N k) (norm_nonneg _)
    · simpa using mul_nonneg (norm_nonneg (u k)) ((norm_nonneg _).trans (hC 0 0))

/-- The `n → ∞` form of the limiting Bailey lemma for the unit Bailey pair, for `‖a‖ ≤ 1`:
`∑_k a^k q^{k²} / (q;q)_k = (aq;q)_∞⁻¹ ∑_k a^{2k} q^{2k²} α_k`. -/
theorem sum_unit_bailey {a q : ℂ} (hq : ‖q‖ < 1) (ha : ‖a‖ ≤ 1) :
    ∑' k : ℕ, a ^ k * q ^ (k * k) * (1 / qPochhammer q q k) =
      (∑' k : ℕ, a ^ k * q ^ (k * k) * (a ^ k * q ^ (k * k) * unitAlpha a q k)) /
        qPochhammerInf (a * q) q := by
  have haq : ‖a * q‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg q) ha) hq
  have hqq : ∀ m, qPochhammer q q m ≠ 0 := qPochhammer_ne_zero_of_norm hq hq
  have haqq : ∀ m, qPochhammer (a * q) q m ≠ 0 := qPochhammer_ne_zero_of_norm haq hq
  have hQ : qPochhammerInf q q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one hq hq
  have hA : qPochhammerInf (a * q) q ≠ 0 := qPochhammerInf_ne_zero_of_norm_lt_one haq hq
  set α1 : ℕ → ℂ := fun k => a ^ k * q ^ (k * k) * unitAlpha a q k with hα1
  set β1 : ℕ → ℂ := fun k => 1 / qPochhammer q q k with hβ1
  -- `(α1, β1)` is a Bailey pair: the limiting Bailey lemma applied to the unit pair
  have pair1 : ∀ k, β1 k = ∑ j ∈ range (k + 1),
      α1 j / (qPochhammer q q (k - j) * qPochhammer (a * q) q (k + j)) := by
    intro k
    have h := bailey_limit_relation (α := unitAlpha a q) (β := fun i => if i = 0 then 1 else 0)
      (n := k) (fun i _ => unit_pair a q i (fun m _ => hqq m) (haqq _)) (fun m _ => hqq m)
      (haqq _)
    rw [sum_eq_single 0 (fun i _ hi => by simp [hi]) (fun h => by simp at h)] at h
    simpa [hβ1, hα1] using h
  -- the relation for `(α1, β1)` at every `N`
  have rel : ∀ N, ∑ k ∈ range (N + 1), a ^ k * q ^ (k * k) * β1 k * (qPochhammer q q (N - k))⁻¹ =
      ∑ k ∈ range (N + 1), a ^ k * q ^ (k * k) * α1 k *
        (qPochhammer q q (N - k) * qPochhammer (a * q) q (N + k))⁻¹ := by
    intro N
    have h := bailey_limit_relation (α := α1) (β := β1) (n := N) (fun k _ => pair1 k)
      (fun m _ => hqq m) (haqq _)
    simpa only [div_eq_mul_inv] using h
  -- bounds
  have tq := tendsto_qPochhammer (w := q) hq
  have taq := tendsto_qPochhammer (w := a * q) hq
  obtain ⟨Cq, hCq⟩ := exists_norm_le_of_tendsto (tq.inv₀ hQ)
  obtain ⟨Ca, hCa⟩ := exists_norm_le_of_tendsto (taq.inv₀ hA)
  obtain ⟨Ba, hBa⟩ := exists_norm_le_of_tendsto taq
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have hgeo : Summable fun k : ℕ => ‖q‖ ^ k := summable_geometric_of_lt_one hq0 hq
  have hpow : ∀ k : ℕ, ‖a‖ ^ k * ‖q‖ ^ (k * k) ≤ ‖q‖ ^ k := by
    intro k
    calc ‖a‖ ^ k * ‖q‖ ^ (k * k) ≤ 1 * ‖q‖ ^ (k * k) :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg a) ha) (by positivity)
      _ ≤ ‖q‖ ^ k := by
          rw [one_mul]
          exact pow_le_pow_of_le_one hq0 hq.le (Nat.le_mul_self k)
  have hCq0 : 0 ≤ Cq := (norm_nonneg _).trans (hCq 0)
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (hCa 0)
  have hBa1 : 1 ≤ Ba := by simpa using hBa 0
  have hunit : ∀ k, ‖unitAlpha a q k‖ ≤ 2 * Ba * Cq := by
    intro k
    have hD : ‖unitD a q k‖ ≤ 2 * Ba := by
      rcases k with _ | k
      · simp [unitD]; linarith
      · simp only [unitD, norm_mul]
        have h1 : ‖1 - a * q ^ (2 * (k + 1))‖ ≤ 2 := by
          calc ‖1 - a * q ^ (2 * (k + 1))‖ ≤ ‖(1 : ℂ)‖ + ‖a * q ^ (2 * (k + 1))‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := by
                rw [norm_one, norm_mul, norm_pow]
                gcongr
                calc ‖a‖ * ‖q‖ ^ (2 * (k + 1)) ≤ 1 * 1 :=
                      mul_le_mul ha (pow_le_one₀ hq0 hq.le) (by positivity) zero_le_one
                  _ = 1 := by norm_num
            _ = 2 := by norm_num
        nlinarith [hBa k, norm_nonneg (qPochhammer (a * q) q k),
          norm_nonneg (1 - a * q ^ (2 * (k + 1)))]
    simp only [unitAlpha, div_eq_mul_inv, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
    have h3 : ‖q‖ ^ k.choose 2 ≤ 1 := pow_le_one₀ hq0 hq.le
    calc ‖unitD a q k‖ * ‖q‖ ^ k.choose 2 * ‖(qPochhammer q q k)⁻¹‖ ≤
          (2 * Ba) * 1 * Cq :=
        mul_le_mul (mul_le_mul hD h3 (by positivity) (by linarith)) (hCq k) (norm_nonneg _)
          (by linarith)
      _ = 2 * Ba * Cq := by ring
  have hsumL : Summable fun k : ℕ => ‖a ^ k * q ^ (k * k) * β1 k‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (hgeo.mul_right Cq)
    simp only [hβ1, norm_mul, norm_pow, one_div, norm_inv]
    exact mul_le_mul (hpow k) (by simpa [norm_inv] using hCq k) (inv_nonneg.mpr (norm_nonneg _))
      (pow_nonneg hq0 k)
  have hsumR : Summable fun k : ℕ => ‖a ^ k * q ^ (k * k) * α1 k‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      (hgeo.mul_right (2 * Ba * Cq))
    simp only [hα1, norm_mul, norm_pow]
    have h1 := hpow k
    have h2 : ‖a‖ ^ k * ‖q‖ ^ (k * k) ≤ 1 :=
      h1.trans (pow_le_one₀ hq0 hq.le)
    calc ‖a‖ ^ k * ‖q‖ ^ (k * k) * (‖a‖ ^ k * ‖q‖ ^ (k * k) * ‖unitAlpha a q k‖) ≤
          ‖q‖ ^ k * (1 * (2 * Ba * Cq)) :=
        mul_le_mul h1 (mul_le_mul h2 (hunit k) (norm_nonneg _) zero_le_one) (by positivity)
          (pow_nonneg hq0 k)
      _ = ‖q‖ ^ k * (2 * Ba * Cq) := by ring
  -- the two limits
  have limL := tendsto_sum_range_mul (u := fun k => a ^ k * q ^ (k * k) * β1 k)
    (v := fun N k => (qPochhammer q q (N - k))⁻¹) (L := (qPochhammerInf q q)⁻¹) hsumL
    (fun k => ((tq.comp (tendsto_sub_atTop_nat k)).inv₀ hQ)) (fun N k => hCq _)
  have limR := tendsto_sum_range_mul (u := fun k => a ^ k * q ^ (k * k) * α1 k)
    (v := fun N k => (qPochhammer q q (N - k) * qPochhammer (a * q) q (N + k))⁻¹)
    (L := (qPochhammerInf q q * qPochhammerInf (a * q) q)⁻¹) hsumR
    (fun k => ((tq.comp (tendsto_sub_atTop_nat k)).mul
      (taq.comp (tendsto_add_atTop_nat k))).inv₀ (mul_ne_zero hQ hA))
    (fun N k => by
      rw [mul_inv, norm_mul]
      exact mul_le_mul (hCq _) (hCa _) (norm_nonneg _) hCq0)
  simp only [rel] at limL
  have heq := tendsto_nhds_unique limL limR
  have hfin : (∑' k, a ^ k * q ^ (k * k) * β1 k) =
      (∑' k, a ^ k * q ^ (k * k) * α1 k) / qPochhammerInf (a * q) q := by
    rw [mul_inv] at heq
    field_simp at heq ⊢
    linear_combination heq
  simpa only [hα1, hβ1] using hfin

/-! ### Rogers–Ramanujan -/

/-- Regrouping the factors of `(q;q)_{5M}` by residue mod `5`. -/
private lemma qPochhammer_five_mul (q : ℂ) (M : ℕ) :
    qPochhammer q q (5 * M) = qPochhammer q (q ^ 5) M * qPochhammer (q ^ 2) (q ^ 5) M *
      qPochhammer (q ^ 3) (q ^ 5) M * qPochhammer (q ^ 4) (q ^ 5) M *
      qPochhammer (q ^ 5) (q ^ 5) M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 5 * (M + 1) = 5 * M + 5 by ring, qPochhammer_add, ih]
    simp only [qPochhammer_succ, qPochhammer_zero]
    ring

/-- `(q;q)_∞ = (q, q², q³, q⁴, q⁵; q⁵)_∞`. -/
theorem qPochhammerInf_mod_five {q : ℂ} (hq : ‖q‖ < 1) :
    qPochhammerInf q q = qPochhammerInf q (q ^ 5) * qPochhammerInf (q ^ 2) (q ^ 5) *
      qPochhammerInf (q ^ 3) (q ^ 5) * qPochhammerInf (q ^ 4) (q ^ 5) *
      qPochhammerInf (q ^ 5) (q ^ 5) := by
  have hq5 : ‖q ^ 5‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have h5 : Tendsto (fun M : ℕ => 5 * M) atTop atTop :=
    tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_left M (by norm_num)) tendsto_id
  have hL := (tendsto_qPochhammer (w := q) hq).comp h5
  have hR := ((((tendsto_qPochhammer (w := q) hq5).mul (tendsto_qPochhammer (w := q ^ 2) hq5)).mul
    (tendsto_qPochhammer (w := q ^ 3) hq5)).mul (tendsto_qPochhammer (w := q ^ 4) hq5)).mul
    (tendsto_qPochhammer (w := q ^ 5) hq5)
  refine tendsto_nhds_unique hL ?_
  refine hR.congr fun M => ?_
  simp only [Function.comp_apply, qPochhammer_five_mul]

private lemma choose_two_cast (m : ℕ) : ((m.choose 2 : ℕ) : ℤ) * 2 = (m : ℤ) * ((m : ℤ) - 1) := by
  have h := two_choose_add m
  zify at h
  linear_combination h

private lemma tri_natCast (m : ℕ) : DLMF.QSeries.TripleProduct.tri (m : ℤ) = (m.choose 2 : ℕ) := by
  have h1 := DLMF.QSeries.TripleProduct.tri_mul_two (m : ℤ)
  have h2 := choose_two_cast m
  omega

private lemma tri_neg_succ (m : ℕ) :
    DLMF.QSeries.TripleProduct.tri (-((m : ℤ) + 1)) = ((m + 1 + 1).choose 2 : ℕ) := by
  have h1 := DLMF.QSeries.TripleProduct.tri_mul_two (-((m : ℤ) + 1))
  have h2 := choose_two_cast (m + 1 + 1)
  push_cast at h2
  have : DLMF.QSeries.TripleProduct.tri (-((m : ℤ) + 1)) * 2 = ((m + 1 + 1).choose 2 : ℕ) * 2 := by
    rw [h1, h2]; ring
  omega

/-- The Jacobi triple product summand at base `q⁵`, evaluated at `n ≥ 0` and `n < 0`. -/
private lemma jtp5_nat (q z : ℂ) (j m : ℕ) (hz : z = q ^ j) :
    (-1 : ℂ) ^ (m : ℤ) * (q ^ 5) ^ (((m : ℤ) : ℂ) * (((m : ℤ) : ℂ) - 1) / 2) * z ^ (m : ℤ) =
      (-1) ^ m * q ^ (5 * m.choose 2 + j * m) := by
  rw [DLMF.QSeries.TripleProduct.cpow_tri, tri_natCast, zpow_natCast, zpow_natCast, zpow_natCast,
    hz, ← pow_mul, ← pow_mul, pow_add, mul_comm j m]
  ring

private lemma jtp5_neg (q z : ℂ) (hq : q ≠ 0) (j m E : ℕ) (hz : z = q ^ j)
    (hE : 5 * (m + 1 + 1).choose 2 = E + j * (m + 1)) :
    (-1 : ℂ) ^ (-((m : ℤ) + 1)) *
        (q ^ 5) ^ (((-((m : ℤ) + 1) : ℤ) : ℂ) * (((-((m : ℤ) + 1) : ℤ) : ℂ) - 1) / 2) *
        z ^ (-((m : ℤ) + 1)) = (-1) ^ (m + 1) * q ^ E := by
  rw [DLMF.QSeries.TripleProduct.cpow_tri, tri_neg_succ, zpow_natCast, hz,
    show -((m : ℤ) + 1) = -((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_neg,
    zpow_natCast, zpow_natCast, ← pow_mul, ← pow_mul, hE, pow_add q E (j * (m + 1))]
  have hs : ((-1 : ℂ) ^ (m + 1))⁻¹ = (-1) ^ (m + 1) := by rw [← inv_pow, inv_neg, inv_one]
  rw [hs]
  have hq' : q ^ (j * (m + 1)) ≠ 0 := pow_ne_zero _ hq
  field_simp

/-- Summability of `n ↦ ± q^{E(n)}` with `E(n) ≥ n`. -/
private lemma summable_sign_pow {q : ℂ} (hq : ‖q‖ < 1) (s : ℕ → ℕ) (E : ℕ → ℕ)
    (hE : ∀ n, n ≤ E n) : Summable fun n => (-1 : ℂ) ^ s n * q ^ E n := by
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg q) hq) fun n => ?_
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg q) hq.le (hE n)

/-- The Jacobi triple product at base `q⁵` and `z = q^j`, split into `n ≥ 0` and `n < 0`. -/
private lemma jtp5_hasSum {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (j : ℕ) (hj : 1 ≤ j)
    (E : ℕ → ℕ)
    (hE : ∀ m, 5 * (m + 1 + 1).choose 2 = E m + j * (m + 1)) (hEm : ∀ m, m ≤ E m) :
    qPochhammerInf (q ^ 5) (q ^ 5) * qPochhammerInf (q ^ j) (q ^ 5) *
        qPochhammerInf (q ^ 5 / q ^ j) (q ^ 5) =
      (∑' m : ℕ, (-1 : ℂ) ^ m * q ^ (5 * m.choose 2 + j * m)) +
        ∑' m : ℕ, (-1 : ℂ) ^ (m + 1) * q ^ E m := by
  have hq5 : ‖q ^ 5‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have hs1 : Summable fun m : ℕ => (-1 : ℂ) ^ m * q ^ (5 * m.choose 2 + j * m) :=
    summable_sign_pow hq (fun m => m) _ fun m => by nlinarith
  have hs2 : Summable fun m : ℕ => (-1 : ℂ) ^ (m + 1) * q ^ E m :=
    summable_sign_pow hq (fun m => m + 1) _ hEm
  rw [jacobi_triple_product hq5 (pow_ne_zero j hq0)]
  refine (HasSum.of_nat_of_neg_add_one ?_ ?_).tsum_eq
  · convert hs1.hasSum using 1
    funext m
    simpa using jtp5_nat q (q ^ j) j m rfl
  · convert hs2.hasSum using 1
    funext m
    simpa using jtp5_neg q (q ^ j) hq0 j m (E m) rfl (hE m)

/-- The first Rogers–Ramanujan identity (AAR §12.1):
`∑ q^{n²} / (q;q)_n = 1 / (q, q⁴; q⁵)_∞`. -/
@[dlmf 17.2.E49]
theorem rogers_ramanujan_first {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' n : ℕ, q ^ (n * n : ℕ) / qPochhammer q q n) =
      1 / (qPochhammerInf q (q ^ 5) * qPochhammerInf (q ^ 4) (q ^ 5)) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow (mul_ne_zero hn hn)])]
    simp [qPochhammerInf]
  have hqk : ∀ k, qPochhammer q q k ≠ 0 := qPochhammer_ne_zero_of_norm hq hq
  have hpos : ∀ r : ℕ, 0 < r → ‖q ^ r‖ < 1 := fun r hr => by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq hr.ne'
  -- the `n → ∞` Bailey identity at `a = 1`
  have hB := sum_unit_bailey (a := 1) hq (by simp)
  simp only [one_pow, one_mul, mul_one_div] at hB
  -- the triple product at base `q⁵`, `z = q²`
  set E : ℕ → ℕ := fun m => 2 * ((m + 1) * (m + 1)) + (m + 1).choose 2 + (m + 1) with hEdef
  have hJ := jtp5_hasSum hq hq0 2 (by norm_num) E (fun m => by
      simp only [hEdef]; rw [choose_two_succ (m + 1)]; nlinarith [two_choose_add (m + 1)])
    (fun m => by simp only [hEdef]; nlinarith)
  rw [show q ^ 5 / q ^ 2 = q ^ 3 by field_simp] at hJ
  set g1 : ℕ → ℂ := fun m => (-1) ^ m * q ^ (5 * m.choose 2 + 2 * m) with hg1
  set g2 : ℕ → ℂ := fun m => (-1) ^ (m + 1) * q ^ E m with hg2
  have hs1 : Summable g1 := summable_sign_pow hq (fun m => m) _ fun m => by omega
  have hs2 : Summable g2 :=
    summable_sign_pow hq (fun m => m + 1) _ fun m => by simp only [hEdef]; nlinarith
  -- the alpha-series term by term
  have hT : ∀ k, q ^ (k * k) * (q ^ (k * k) * unitAlpha 1 q k) =
      if k = 0 then g1 0 else g1 k + g2 (k - 1) := by
    intro k
    rcases k with _ | k
    · simp [unitAlpha, unitD, hg1]
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, hg1, hg2, hEdef, Nat.add_sub_cancel,
        unitAlpha, unitD, one_mul]
      rw [qPochhammer_succ q q k,
        show 5 * (k + 1).choose 2 + 2 * (k + 1) = 2 * ((k + 1) * (k + 1)) + (k + 1).choose 2 by
          nlinarith [two_choose_add (k + 1)]]
      have h1 := one_sub_mul_pow_ne_zero_of_norm hq hq k
      have h0 := hqk k
      field_simp
      ring
  have hTsum : (∑' k : ℕ, q ^ (k * k) * (q ^ (k * k) * unitAlpha 1 q k)) =
      ∑' m, g1 m + ∑' m, g2 m := by
    set T : ℕ → ℂ := fun k => q ^ (k * k) * (q ^ (k * k) * unitAlpha 1 q k) with hTdef
    have h1 : HasSum (fun k => g1 (k + 1)) (∑' k, g1 (k + 1)) :=
      ((summable_nat_add_iff 1).mpr hs1).hasSum
    have h3 : HasSum (fun n => T (n + 1)) (∑' k, g1 (k + 1) + ∑' m, g2 m) := by
      convert h1.add hs2.hasSum using 1
      funext n
      simp only [hTdef, hT (n + 1), Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have h4 := h3.zero_add
    rw [h4.tsum_eq, hs1.tsum_eq_zero_add]
    simp only [hTdef, hT 0, ↓reduceIte]
    ring
  rw [hB, hTsum, ← hJ, qPochhammerInf_mod_five hq]
  have n1 := qPochhammerInf_ne_zero_of_norm_lt_one hq (hpos 5 (by norm_num))
  have n2 := qPochhammerInf_ne_zero_of_norm_lt_one (hpos 2 (by norm_num)) (hpos 5 (by norm_num))
  have n3 := qPochhammerInf_ne_zero_of_norm_lt_one (hpos 3 (by norm_num)) (hpos 5 (by norm_num))
  have n4 := qPochhammerInf_ne_zero_of_norm_lt_one (hpos 4 (by norm_num)) (hpos 5 (by norm_num))
  have n5 := qPochhammerInf_ne_zero_of_norm_lt_one (hpos 5 (by norm_num)) (hpos 5 (by norm_num))
  field_simp

/-- The second Rogers–Ramanujan identity:
`∑ q^{n(n+1)} / (q;q)_n = 1 / (q², q³; q⁵)_∞`. -/
@[dlmf 17.2.E50]
theorem rogers_ramanujan_second {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' n : ℕ, q ^ (n * (n + 1) : ℕ) / qPochhammer q q n) =
      1 / (qPochhammerInf (q ^ 2) (q ^ 5) * qPochhammerInf (q ^ 3) (q ^ 5)) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow (mul_ne_zero hn (Nat.succ_ne_zero n))])]
    simp [qPochhammerInf]
  have hpos : ∀ r : ℕ, 0 < r → ‖q ^ r‖ < 1 := fun r hr => by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq hr.ne'
  have h1q : (1 : ℂ) - q ≠ 0 := one_sub_ne_zero_of_norm_lt_one hq
  -- the `n → ∞` Bailey identity at `a = q`
  have hB := sum_unit_bailey (a := q) hq hq.le
  simp only [mul_one_div] at hB
  -- the triple product at base `q⁵`, `z = q⁴`
  set E : ℕ → ℕ := fun m => 2 * (m * m) + 4 * m + 1 + m.choose 2 with hEdef
  have hJ := jtp5_hasSum hq hq0 4 (by norm_num) E (fun m => by
      simp only [hEdef]; rw [choose_two_succ (m + 1), choose_two_succ m]
      nlinarith [two_choose_add m])
    (fun m => by simp only [hEdef]; nlinarith)
  rw [show q ^ 5 / q ^ 4 = q by field_simp] at hJ
  set g1 : ℕ → ℂ := fun m => (-1) ^ m * q ^ (5 * m.choose 2 + 4 * m) with hg1
  set g2 : ℕ → ℂ := fun m => (-1) ^ (m + 1) * q ^ E m with hg2
  have hs1 : Summable g1 := summable_sign_pow hq (fun m => m) _ fun m => by omega
  have hs2 : Summable g2 :=
    summable_sign_pow hq (fun m => m + 1) _ fun m => by simp only [hEdef]; nlinarith
  -- `(1 - q)` times the alpha-series, term by term
  have hT : ∀ k, (1 - q) * (q ^ k * q ^ (k * k) * (q ^ k * q ^ (k * k) * unitAlpha q q k)) =
      g1 k + g2 k := by
    intro k
    rcases k with _ | k
    · simp [unitAlpha, unitD, hg1, hg2, hEdef]; ring
    · simp only [hg1, hg2, hEdef, unitAlpha, unitD]
      rw [show qPochhammer q q (k + 1) = (1 - q) * qPochhammer (q * q) q k from
          qPochhammer_succ' q q k,
        show 5 * (k + 1).choose 2 + 4 * (k + 1) =
          2 * ((k + 1) * (k + 1)) + 2 * (k + 1) + (k + 1).choose 2 by
          nlinarith [two_choose_add (k + 1)]]
      have h2 := qPochhammer_ne_zero_of_norm (x := q * q) (q := q)
        (by rw [norm_mul]; nlinarith [norm_nonneg q]) hq k
      have h2' : qPochhammer (q ^ 2) q k ≠ 0 := by rwa [sq]
      field_simp
      ring
  have hTsum : (∑' k : ℕ, q ^ k * q ^ (k * k) * (q ^ k * q ^ (k * k) * unitAlpha q q k)) =
      (∑' m, g1 m + ∑' m, g2 m) / (1 - q) := by
    rw [eq_div_iff h1q, mul_comm, ← tsum_mul_left]
    refine HasSum.tsum_eq ?_
    convert hs1.hasSum.add hs2.hasSum using 1
    funext k
    exact hT k
  have hshift : qPochhammerInf q q = (1 - q) * qPochhammerInf (q * q) q := qPochhammerInf_shift hq
  have hL : (∑' n : ℕ, q ^ (n * (n + 1) : ℕ) / qPochhammer q q n) =
      ∑' k : ℕ, q ^ k * q ^ (k * k) / qPochhammer q q k := by
    refine tsum_congr fun n => ?_
    rw [show n * (n + 1) = n + n * n by ring, pow_add]
  rw [hL, hB, hTsum, ← hJ]
  have hQ := qPochhammerInf_mod_five hq
  have hm : qPochhammerInf (q * q) q = qPochhammerInf q q / (1 - q) := by
    rw [hshift]; field_simp
  rw [hm, hQ]
  have n1 := qPochhammerInf_ne_zero_of_norm_lt_one hq (hpos 5 (by norm_num))
  have n2 := qPochhammerInf_ne_zero_of_norm_lt_one (hpos 2 (by norm_num)) (hpos 5 (by norm_num))
  have n3 := qPochhammerInf_ne_zero_of_norm_lt_one (hpos 3 (by norm_num)) (hpos 5 (by norm_num))
  have n4 := qPochhammerInf_ne_zero_of_norm_lt_one (hpos 4 (by norm_num)) (hpos 5 (by norm_num))
  have n5 := qPochhammerInf_ne_zero_of_norm_lt_one (hpos 5 (by norm_num)) (hpos 5 (by norm_num))
  field_simp

end DLMF.Bailey
