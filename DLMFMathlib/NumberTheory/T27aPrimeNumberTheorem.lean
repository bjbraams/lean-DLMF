/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.PrimeIdealTheorem
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.PrimesCongruent

/-!
# The prime number theorem for `Nat.primeCounting`

TauCeti proves the prime ideal theorem for every number field `K`
(`TauCeti.primeCount_univ_isEquivalent_div_log`) and the prime number theorem in arithmetic
progressions over `ℚ` (`NumberField.Chebotarev.tendsto_primeCount_primesCongruent`), both
for the count `TauCeti.primeCount` of height-one primes of `𝓞 K` by absolute norm. Here the
case `K = ℚ` is transported to Mathlib's `Nat.primeCounting`: the absolute norm
`v ↦ N(v)` is a bijection from the height-one primes of `𝓞 ℚ` onto the rational primes
(`Rat.HeightOneSpectrum.primesEquiv`, `Rat.HeightOneSpectrum.absNorm_asIdeal`).

## Main results

* `Nat.t27a_primeCounting_isEquivalent`: `π(⌊x⌋) ~ x / log x` as `x → ∞` over `ℝ`.
* `Nat.t27a_primeCounting_isEquivalent_nat`: `π(n) ~ n / log n` over `ℕ`.
* `Nat.t27a_nth_prime_isEquivalent`: `p_n ~ n log n` (with Mathlib's indexing from `0`).
* `Chebyshev.t27a_theta_isEquivalent`, `Chebyshev.t27a_psi_isEquivalent`: `θ(x) ~ x`,
  `ψ(x) ~ x`.
* `Nat.t27a_primesLE_modEq_isEquivalent`: the number of primes `p ≤ x` with `p ≡ a (mod m)`,
  `(a, m) = 1`, is asymptotic to `x / (φ(m) log x)`.

Credit: the analytic content is TauCeti's (`TauCeti.primeCount_univ_isEquivalent_div_log`,
`TauCeti.primeIdealTheorem`,
`NumberField.Chebotarev.tendsto_primeCount_primesCongruent`,
`Rat.HeightOneSpectrum.absNorm_asIdeal`).
-/

@[expose] public section

open Filter Asymptotics IsDedekindDomain
open scoped NumberField

namespace Nat

/-- Counting height-one primes of `𝓞 ℚ` of norm at most `x` with a property of the norm is
counting rational primes `p ≤ ⌊x⌋₊` with that property. -/
theorem t27a_card_primesLE_filter (P : ℕ → Prop) [DecidablePred P] (x : ℝ) :
    ((TauCeti.primesLE ℚ x).filter (fun v ↦ P (Ideal.absNorm v.asIdeal))).card =
      ((Nat.primesLE ⌊x⌋₊).filter P).card := by
  classical
  refine Finset.card_bij (fun v _ ↦ Ideal.absNorm v.asIdeal) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, TauCeti.mem_normLE] at hv
    rw [Finset.mem_filter, Nat.mem_primesLE]
    refine ⟨⟨Nat.le_floor hv.1, ?_⟩, hv.2⟩
    rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
    exact Rat.HeightOneSpectrum.prime_natGenerator v
  · intro v _ w _ hvw
    apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
    apply Subtype.ext
    change Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator w
    simpa using hvw
  · intro p hp
    rw [Finset.mem_filter, Nat.mem_primesLE] at hp
    obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp.1.2
    refine ⟨v, ?_, hv⟩
    simp only [Finset.mem_filter, TauCeti.mem_normLE, hv]
    refine ⟨?_, hp.2⟩
    have hx : 0 ≤ x := by
      by_contra h
      have := hp.1.2.two_le
      rw [Nat.floor_eq_zero.mpr (by linarith [not_le.mp h])] at hp
      omega
    exact (Nat.cast_le.mpr hp.1.1).trans (Nat.floor_le hx)

/-- Summing a function of the norm over the height-one primes of `𝓞 ℚ` of norm at most `x` is
summing it over the rational primes `p ≤ ⌊x⌋₊`. -/
theorem t27a_sum_primesLE {M : Type*} [AddCommMonoid M] (g : ℕ → M) (x : ℝ) :
    ∑ v ∈ TauCeti.primesLE ℚ x, g (Ideal.absNorm v.asIdeal) =
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, g p := by
  classical
  have h := Finset.sum_image (s := TauCeti.primesLE ℚ x) (f := g)
    (g := fun v ↦ Ideal.absNorm v.asIdeal) (fun v _ w _ hvw ↦ by
      apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
      apply Subtype.ext
      change Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator w
      simpa using hvw)
  rw [← h]
  congr 1
  ext p
  have hc := t27a_card_primesLE_filter (· = p) x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have : 0 < ((TauCeti.primesLE ℚ x).filter
        (fun w ↦ Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal)).card :=
      Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, rfl⟩⟩
    rw [hc] at this
    obtain ⟨q, hq⟩ := Finset.card_pos.mp this
    rw [Finset.mem_filter] at hq
    exact hq.2 ▸ hq.1
  · intro hp
    have : 0 < ((Nat.primesLE ⌊x⌋₊).filter (· = p)).card :=
      Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
    rw [← hc] at this
    obtain ⟨v, hv⟩ := Finset.card_pos.mp this
    rw [Finset.mem_filter] at hv
    exact ⟨v, hv⟩

/-- `TauCeti.primeCount ℚ Set.univ x` is the classical prime counting function `π(⌊x⌋₊)`. -/
theorem t27a_primeCount_rat_univ (x : ℝ) :
    TauCeti.primeCount ℚ Set.univ x = (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  classical
  rw [TauCeti.primeCount_eq_card, ← Nat.primesLE_card_eq_primeCounting]
  have h := t27a_card_primesLE_filter (fun _ ↦ True) x
  simpa using h

/-- **The prime number theorem** over `ℝ`: `π(⌊x⌋₊) ~ x / log x` as `x → ∞`. -/
theorem t27a_primeCounting_isEquivalent :
    (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] fun x ↦ x / Real.log x :=
  (TauCeti.primeCount_univ_isEquivalent_div_log ℚ).congr_left
    (Eventually.of_forall t27a_primeCount_rat_univ)

/-- **The prime number theorem** over `ℕ`: `π(n) ~ n / log n` as `n → ∞`. -/
theorem t27a_primeCounting_isEquivalent_nat :
    (fun n : ℕ ↦ (Nat.primeCounting n : ℝ)) ~[atTop] fun n ↦ (n : ℝ) / Real.log n := by
  have h := t27a_primeCounting_isEquivalent.comp_tendsto tendsto_natCast_atTop_atTop
  refine h.congr_left (Eventually.of_forall fun n ↦ ?_)
  simp

/-- `π(p_k) = k + 1` for the `k`th prime `p_k = nth Nat.Prime k` (indexed from `0`). -/
theorem t27a_primeCounting_nth_prime (k : ℕ) : Nat.primeCounting (nth Nat.Prime k) = k + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, ← Nat.primeCounting',
    Nat.primeCounting'_nth_eq]
  simp

/-- `n + 1 ~ n` along `ℕ`, as real numbers. -/
theorem t27a_natCast_add_one_isEquivalent :
    (fun n : ℕ ↦ (n : ℝ) + 1) ~[atTop] fun n ↦ (n : ℝ) := by
  refine IsLittleO.isEquivalent ?_
  have h : (fun _ : ℕ ↦ (1 : ℝ)) =o[atTop] fun n ↦ (n : ℝ) :=
    (isLittleO_one_left_iff ℝ).mpr
      (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop)
  refine h.congr_left fun n ↦ ?_
  simp

/-- **The `n`th prime**: `p_n ~ n log n` (Mathlib's indexing `p_n = nth Nat.Prime n`). -/
theorem t27a_nth_prime_isEquivalent :
    (fun n : ℕ ↦ (nth Nat.Prime n : ℝ)) ~[atTop] fun n ↦ (n : ℝ) * Real.log n := by
  set f : ℕ → ℝ := fun n ↦ (nth Nat.Prime n : ℝ) with hf_def
  have hq : Tendsto (nth Nat.Prime) atTop atTop :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  have hf : Tendsto f atTop atTop := tendsto_natCast_atTop_atTop.comp hq
  -- `n + 1 = π(p_n) ~ p_n / log p_n`
  have h1 : (fun n : ℕ ↦ (n : ℝ)) ~[atTop] fun n ↦ f n / Real.log (f n) := by
    have h := t27a_primeCounting_isEquivalent_nat.comp_tendsto hq
    refine t27a_natCast_add_one_isEquivalent.symm.trans (h.congr_left ?_)
    refine Eventually.of_forall fun n ↦ ?_
    simp [t27a_primeCounting_nth_prime]
  have hg : Tendsto (fun n ↦ f n / Real.log (f n)) atTop atTop :=
    h1.tendsto_atTop tendsto_natCast_atTop_atTop
  -- `log n ~ log (p_n / log p_n) ~ log p_n`
  have h2 : (fun n : ℕ ↦ Real.log n) ~[atTop] fun n ↦ Real.log (f n) := by
    refine (h1.log hg).trans ?_
    refine IsLittleO.isEquivalent ?_
    have hll : (fun n ↦ Real.log (Real.log (f n))) =o[atTop] fun n ↦ Real.log (f n) :=
      Real.isLittleO_log_id_atTop.comp_tendsto (Real.tendsto_log_atTop.comp hf)
    refine hll.neg_left.congr' ?_ EventuallyEq.rfl
    filter_upwards [hf.eventually_gt_atTop 1] with n hn
    have hlog : 0 < Real.log (f n) := Real.log_pos hn
    simp only [Pi.sub_apply]
    rw [Real.log_div (by linarith) hlog.ne']
    ring
  have h3 := (h1.mul h2).symm
  refine h3.congr_left ?_
  filter_upwards [hf.eventually_gt_atTop 1] with n hn
  have hlog : 0 < Real.log (f n) := Real.log_pos hn
  simp only [Pi.mul_apply]
  field_simp

/-- **The prime number theorem in arithmetic progressions**: for `m > 0` and `(a, m) = 1`, the
number of primes `p ≤ x` with `p ≡ a (mod m)` is asymptotic to `x / (φ(m) log x)`.
This is a natural-density (counting) statement, from TauCeti's
`NumberField.Chebotarev.tendsto_primeCount_primesCongruent`. -/
theorem t27a_primesLE_modEq_isEquivalent {m a : ℕ} (hm : 0 < m) (ha : a.Coprime m) :
    (fun x : ℝ ↦ (((Nat.primesLE ⌊x⌋₊).filter (fun p ↦ p ≡ a [MOD m])).card : ℝ)) ~[atTop]
      fun x ↦ x / (m.totient * Real.log x) := by
  classical
  have : NeZero m := ⟨hm.ne'⟩
  have hu : IsUnit (a : ZMod m) := (ZMod.isUnit_iff_coprime a m).mpr ha
  have h := NumberField.Chebotarev.tendsto_primeCount_primesCongruent m a hu
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hcount : ∀ x : ℝ, TauCeti.primeCount ℚ
      {p : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm p.asIdeal % m = a % m} x =
      (((Nat.primesLE ⌊x⌋₊).filter (fun p ↦ p ≡ a [MOD m])).card : ℝ) := by
    intro x
    rw [TauCeti.primeCount_eq_card]
    exact_mod_cast t27a_card_primesLE_filter (fun p ↦ p ≡ a [MOD m]) x
  simp only [hcount] at h
  have hv : ∀ᶠ x : ℝ in atTop, x / (m.totient * Real.log x) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    have := Real.log_pos hx
    positivity
  rw [isEquivalent_iff_tendsto_one hv]
  have h' := h.const_mul (m.totient : ℝ)
  rw [mul_one_div_cancel hφ.ne'] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have := Real.log_pos hx
  simp only [Pi.div_apply]
  field_simp

end Nat

namespace Chebyshev

/-- `TauCeti.primeTheta ℚ Set.univ` is Chebyshev's `θ`. -/
theorem t27a_primeTheta_rat_univ (x : ℝ) : TauCeti.primeTheta ℚ Set.univ x = θ x := by
  rw [TauCeti.primeTheta_apply, theta_eq_sum_primesLE]
  simpa using Nat.t27a_sum_primesLE (fun n ↦ Real.log n) x

/-- **The prime number theorem** for Chebyshev's `θ`: `θ(x) ~ x`. -/
theorem t27a_theta_isEquivalent : θ ~[atTop] fun x : ℝ ↦ x :=
  (TauCeti.primeIdealTheorem ℚ).2.1.congr_left
    (Eventually.of_forall t27a_primeTheta_rat_univ)

/-- **The prime number theorem** for Chebyshev's `ψ`: `ψ(x) ~ x`. -/
theorem t27a_psi_isEquivalent : ψ ~[atTop] fun x : ℝ ↦ x := by
  refine IsLittleO.isEquivalent ?_
  have hs : Real.sqrt =o[atTop] fun x : ℝ ↦ x := by
    refine isLittleO_iff.mpr fun c hc ↦ ?_
    filter_upwards [eventually_ge_atTop (1 / c ^ 2), eventually_gt_atTop 0] with x hx hx0
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg x), Real.norm_of_nonneg hx0.le]
    have hsx : 1 / c ≤ √x := by
      rw [show 1 / c = √((1 / c) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt (by simpa [div_pow] using hx)
    have h1 : 1 ≤ c * √x := by rwa [div_le_iff₀ hc, mul_comm] at hsx
    calc √x = √x * 1 := (mul_one _).symm
      _ ≤ √x * (c * √x) := by gcongr
      _ = c * x := by
        rw [← mul_assoc, mul_comm (√x) c, mul_assoc, Real.mul_self_sqrt hx0.le]
  have h1 : (ψ - θ) =o[atTop] fun x : ℝ ↦ x :=
    isBigO_psi_sub_theta_sqrt.trans_isLittleO hs
  have h2 := t27a_theta_isEquivalent.isLittleO
  refine (h1.add h2).congr_left fun x ↦ ?_
  simp

end Chebyshev
