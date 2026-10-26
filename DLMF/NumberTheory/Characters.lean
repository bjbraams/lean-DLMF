/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.NumberTheory.Functions
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Dirichlet characters, quadratic characters, periodic functions (DLMF §§27.8–27.10)

DLMF defines a Dirichlet character mod `k` as a function on the positive integers with the
four properties 27.8.1–27.8.4 (`IsDirichletCharacterFn`). Mathlib's
`DirichletCharacter ℂ k` (a multiplicative character of `ZMod k`) is the same object:
`DirichletCharacter.isDirichletCharacterFn` shows that `n ↦ χ n` has the four properties.
Mathlib's `legendreSym p a` and `jacobiSym a P` (`J(a | P)`) are DLMF's `(a|p)` and `(a|P)`.

The exponentials `e^{2πimn/k}` of §27.10 are written `Complex.exp (2πi m n / k)`;
`ramanujanSum k n` is `c_k(n)` (27.10.4) and `gaussSumDLMF χ n` is `G(n, χ)` (27.10.9),
DLMF's sum over `m = 1, …, k`. Mathlib's `gaussSum χ ψ` sums over `ZMod k` with an additive
character `ψ`; `G(n, χ)` is `gaussSum χ (ZMod.stdAddChar.mulShift n)`.
-/

@[expose] public noncomputable section

open Finset Complex ArithmeticFunction
open scoped ArithmeticFunction.Moebius Real

namespace DLMF.NumberTheory

/-! ### §27.8 Dirichlet characters -/

/-- DLMF 27.8.1–27.8.4: `χ` is a Dirichlet character mod `k` if `χ(1) = 1`,
`χ(mn) = χ(m)χ(n)`, `χ(n + k) = χ(n)` (`m, n = 1, 2, …`) and `χ(n) = 0` when `(n, k) > 1`. -/
@[dlmf 27.8.E1, dlmf 27.8.E2, dlmf 27.8.E3, dlmf 27.8.E4]
def IsDirichletCharacterFn (k : ℕ) (χ : ℕ → ℂ) : Prop :=
  χ 1 = 1 ∧ (∀ m n : ℕ, 0 < m → 0 < n → χ (m * n) = χ m * χ n) ∧
    (∀ n : ℕ, 0 < n → χ (n + k) = χ n) ∧ ∀ n : ℕ, 0 < n → n.gcd k ≠ 1 → χ n = 0

/-- Every Mathlib Dirichlet character `χ : DirichletCharacter ℂ k` satisfies 27.8.1–27.8.4. -/
@[dlmf 27.8.E1, dlmf 27.8.E2, dlmf 27.8.E3, dlmf 27.8.E4]
theorem _root_.DirichletCharacter.isDirichletCharacterFn {k : ℕ} (χ : DirichletCharacter ℂ k) :
    IsDirichletCharacterFn k fun n ↦ χ n := by
  refine ⟨by simp, fun m n _ _ ↦ by simp, fun n _ ↦ by simp, fun n _ hn ↦ ?_⟩
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  exact hn

/-- A function with the properties 27.8.1–27.8.4 only depends on `n mod k` (`n ≥ 1`). -/
theorem r27_apply_eq_mod_add {k : ℕ} (hk : 0 < k) {f : ℕ → ℂ} (hf : IsDirichletCharacterFn k f)
    {a : ℕ} (ha : 0 < a) : f a = f (a % k + k) := by
  have hq : ∀ r, 0 < r → ∀ q, f (r + k * q) = f r := by
    intro r hr q
    induction q with
    | zero => simp
    | succ q ih => rw [mul_add, mul_one, ← add_assoc, hf.2.2.1 _ (by positivity), ih]
  rcases Nat.eq_zero_or_pos (a % k) with h0 | hpos
  · have hdiv : 1 ≤ a / k :=
      (Nat.one_le_div_iff hk).mpr (Nat.le_of_dvd ha (Nat.dvd_of_mod_eq_zero h0))
    have h1 : a = k + k * (a / k - 1) := by
      have := Nat.div_add_mod a k
      rw [h0, add_zero] at this
      calc a = k * (a / k) := this.symm
        _ = k * (1 + (a / k - 1)) := by congr 1; omega
        _ = k + k * (a / k - 1) := by ring
    rw [h0, zero_add]
    conv_lhs => rw [h1]
    rw [hq k hk]
  · have := Nat.mod_add_div a k
    conv_lhs => rw [← this]
    rw [hq _ hpos, hf.2.2.1 _ hpos]

/-- §27.8 after 27.8.4: conversely, every function with the four properties is a Mathlib
Dirichlet character (for `k ≥ 1`). -/
@[dlmf 27.8]
theorem IsDirichletCharacterFn.exists_dirichletCharacter {k : ℕ} (hk : 0 < k) {f : ℕ → ℂ}
    (hf : IsDirichletCharacterFn k f) :
    ∃ χ : DirichletCharacter ℂ k, ∀ n, 0 < n → f n = χ n := by
  have : NeZero k := ⟨hk.ne'⟩
  have hval : ∀ n : ℕ, ((n : ZMod k)).val = n % k := fun n ↦ ZMod.val_natCast k n
  let χ : DirichletCharacter ℂ k :=
    { toFun := fun x ↦ f (x.val + k)
      map_one' := by
        show f ((1 : ZMod k).val + k) = 1
        rw [show (1 : ZMod k) = ((1 : ℕ) : ZMod k) by simp, hval,
          ← r27_apply_eq_mod_add hk hf one_pos, hf.1]
      map_mul' := by
        intro x y
        show f ((x * y).val + k) = f (x.val + k) * f (y.val + k)
        rw [← hf.2.1 _ _ (by omega) (by omega), r27_apply_eq_mod_add hk hf (a := (x.val + k) * _)
          (by positivity), ZMod.val_mul]
        congr 2
        rw [Nat.mul_mod (x.val + k), Nat.add_mod_right, Nat.add_mod_right, ← Nat.mul_mod]
      map_nonunit' := by
        intro x hx
        show f (x.val + k) = 0
        apply hf.2.2.2 _ (by omega)
        rw [Nat.gcd_add_self_left]
        intro h
        apply hx
        rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
        exact h }
  refine ⟨χ, fun n hn ↦ ?_⟩
  show f n = f ((n : ZMod k).val + k)
  rw [hval, ← r27_apply_eq_mod_add hk hf hn]

/-- DLMF 27.8.5: the principal character `χ₁ (mod k)` is `1` for `(n, k) = 1` and `0`
otherwise; it is Mathlib's `1 : DirichletCharacter ℂ k`. -/
@[dlmf 27.8.E5]
theorem principalCharacter_apply (k n : ℕ) :
    (1 : DirichletCharacter ℂ k) n = if n.Coprime k then 1 else 0 := by
  split_ifs with h
  · exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n k).mpr h)
  · exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])

/-- §27.8 after 27.8.5: `χ(n) ≠ 0` iff `(n, k) = 1`, and then `χ(n)^{φ(k)} = 1`. -/
@[dlmf 27.8]
theorem DirichletCharacter.apply_ne_zero_iff {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    (n : ℕ) : (χ n ≠ 0 ↔ n.Coprime k) ∧ (n.Coprime k → χ n ^ k.totient = 1) := by
  refine ⟨⟨fun h ↦ ?_, fun h ↦ ?_⟩, fun h ↦ ?_⟩
  · by_contra hc
    exact h (MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime]))
  · exact (((ZMod.isUnit_iff_coprime n k).mpr h).map χ).ne_zero
  · obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime n k).mpr h
    rw [← hu, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]

/-- §27.8 after 27.8.5: there are exactly `φ(k)` Dirichlet characters mod `k`. -/
@[dlmf 27.8]
theorem card_dirichletCharacter (k : ℕ) [NeZero k] :
    Nat.card (DirichletCharacter ℂ k) = k.totient := by
  have : NeZero ((Monoid.exponent (ZMod k)ˣ : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ k

/-- The conjugate character (proof of `DirichletCharacter.exists_conj`). -/
theorem q27_exists_conj {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :
    ∃ ψ : DirichletCharacter ℂ k, ∀ n : ℕ, ψ n = starRingEnd ℂ (χ n) :=
  ⟨star χ, fun n ↦ by rw [MulChar.star_apply]; rfl⟩

/-- §27.8 after 27.8.5: the complex conjugate of a character mod `k` is a character mod `k`. -/
@[dlmf 27.8]
theorem DirichletCharacter.exists_conj {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :
    ∃ ψ : DirichletCharacter ℂ k, ∀ n : ℕ, ψ n = starRingEnd ℂ (χ n) :=
  q27_exists_conj χ

/-- DLMF 27.8.6 (proof). -/
theorem q27_sum_dirichletCharacter_mul_conj (k : ℕ) [NeZero k] (m n : ℕ) (hn : n.Coprime k) :
    ∑ χ : DirichletCharacter ℂ k, χ m * starRingEnd ℂ (χ n) =
      if m ≡ n [MOD k] then (k.totient : ℂ) else 0 := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime n k).mpr hn
  have hconj : ∀ χ : DirichletCharacter ℂ k,
      starRingEnd ℂ (χ n) = χ ((u⁻¹ : (ZMod k)ˣ) : ZMod k) := by
    intro χ
    have h1 : starRingEnd ℂ (χ n) = χ⁻¹ n := MulChar.star_apply' χ _
    rw [h1, ← hu, MulChar.inv_apply_eq_inv']
    exact (eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])).symm
  simp_rw [hconj, ← map_mul]
  rw [DirichletCharacter.sum_characters_eq]
  congr 1
  apply propext
  rw [← ZMod.natCast_eq_natCast_iff, ← hu]
  constructor
  · intro h
    have := congrArg (· * (u : ZMod k)) h
    simpa [mul_assoc] using this
  · intro h
    rw [h]; simp

/-- DLMF 27.8.6, orthogonality: for `(n, k) = 1`,
`∑_χ χ(m) χ̄(n) = φ(k)` if `m ≡ n (mod k)` and `0` otherwise. -/
@[dlmf 27.8.E6]
theorem sum_dirichletCharacter_mul_conj (k : ℕ) [NeZero k] (m n : ℕ) (hn : n.Coprime k) :
    ∑ χ : DirichletCharacter ℂ k, χ m * starRingEnd ℂ (χ n) =
      if m ≡ n [MOD k] then (k.totient : ℂ) else 0 :=
  q27_sum_dirichletCharacter_mul_conj k m n hn

/-- §27.8 after 27.8.6: DLMF's definition of a primitive character mod `k`: for every divisor
`d < k` of `k` there is `a ≡ 1 (mod d)` with `(a, k) = 1` and `χ(a) ≠ 1`. -/
@[dlmf 27.8]
def IsPrimitiveDLMF {k : ℕ} (χ : DirichletCharacter ℂ k) : Prop :=
  ∀ d, d ∣ k → d < k → ∃ a : ℕ, a ≡ 1 [MOD d] ∧ a.Coprime k ∧ χ a ≠ 1

/-- `χ(a) = χ₀(a)` for the primitive character `χ₀` and `(a, k) = 1`. -/
theorem q27_apply_eq_primitiveCharacter {k : ℕ} (χ : DirichletCharacter ℂ k) (a : ℕ)
    (ha : a.Coprime k) : χ a = χ.primitiveCharacter a := by
  have := χ.primitiveCharacter_apply_of_isCoprime (a := (a : ℤ))
    (Nat.isCoprime_iff_coprime.mpr ha)
  simpa using this.symm

/-- `χ(a) = 1` when `(a, k) = 1` and `a ≡ 1` modulo the conductor. -/
theorem q27_apply_eq_one_of_modEq_conductor {k : ℕ} (χ : DirichletCharacter ℂ k) (a : ℕ)
    (ha : a.Coprime k) (hmod : a ≡ 1 [MOD χ.conductor]) : χ a = 1 := by
  rw [q27_apply_eq_primitiveCharacter χ a ha]
  have : (a : ZMod χ.conductor) = 1 := by
    rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]; exact hmod
  rw [this, map_one]

/-- DLMF primitivity agrees with Mathlib's (proof). -/
theorem q27_isPrimitiveDLMF_iff {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :
    IsPrimitiveDLMF χ ↔ χ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  constructor
  · intro h
    by_contra hne
    have hd := χ.conductor_dvd_level
    have hlt : χ.conductor < k :=
      lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne k)) hd) hne
    obtain ⟨a, ha1, hak, hχa⟩ := h _ hd hlt
    exact hχa (q27_apply_eq_one_of_modEq_conductor χ a hak ha1)
  · intro hc d hd hdk
    by_contra hcon
    push Not at hcon
    have hf : χ.FactorsThrough d := by
      refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr fun x hx ↦ ?_
      rw [MonoidHom.mem_ker] at hx ⊢
      have hval : ((x : ZMod k).val : ZMod d) = 1 := by
        have := congrArg (fun y : (ZMod d)ˣ ↦ (y : ZMod d)) hx
        simp only [ZMod.unitsMap_val, Units.val_one] at this
        rwa [ZMod.cast_eq_val] at this
      have h1 := hcon (x : ZMod k).val (by
        rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]; exact hval)
        (ZMod.val_coe_unit_coprime x)
      rw [ZMod.natCast_zmod_val] at h1
      ext
      rw [MulChar.coe_toUnitHom, h1, Units.val_one]
    have h1 := DirichletCharacter.conductor_dvd_of_mem_conductorSet χ hf
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact NeZero.ne k (zero_dvd_iff.mp hd))
    have := Nat.le_of_dvd hd0 h1
    omega

/-- DLMF's primitivity is Mathlib's `DirichletCharacter.IsPrimitive` (conductor = level). -/
@[dlmf 27.8]
theorem isPrimitiveDLMF_iff {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :
    IsPrimitiveDLMF χ ↔ χ.IsPrimitive :=
  q27_isPrimitiveDLMF_iff χ

/-- Nonprincipal characters to a prime modulus are primitive (proof). -/
theorem q27_isPrimitive_of_prime {k : ℕ} (hk : k.Prime) (χ : DirichletCharacter ℂ k)
    (hχ : χ ≠ 1) : χ.IsPrimitive := by
  have : NeZero k := ⟨hk.ne_zero⟩
  rcases (Nat.dvd_prime hk).mp χ.conductor_dvd_level with h | h
  · exact absurd ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h) hχ
  · exact h

/-- §27.8: for prime `k`, every nonprincipal character mod `k` is primitive. -/
@[dlmf 27.8]
theorem isPrimitive_of_prime {k : ℕ} (hk : k.Prime) (χ : DirichletCharacter ℂ k) (hχ : χ ≠ 1) :
    χ.IsPrimitive :=
  q27_isPrimitive_of_prime hk χ hχ

/-- DLMF 27.8.7: a divisor `d` of `k` is an induced modulus for `χ` if `χ(a) = 1` for all
`a ≡ 1 (mod d)` with `(a, k) = 1`. -/
@[dlmf 27.8.E7]
def IsInducedModulus {k : ℕ} (χ : DirichletCharacter ℂ k) (d : ℕ) : Prop :=
  d ∣ k ∧ ∀ a : ℕ, a.Coprime k → a ≡ 1 [MOD d] → χ a = 1

/-- DLMF 27.8.8 (proof), with `χ₀` the primitive character. -/
theorem q27_eq_mul_principal {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :
    IsInducedModulus χ χ.conductor ∧ ∃ χ₀ : DirichletCharacter ℂ χ.conductor,
      ∀ n : ℕ, χ n = χ₀ n * (1 : DirichletCharacter ℂ k) n := by
  refine ⟨⟨χ.conductor_dvd_level, fun a ha hmod ↦ q27_apply_eq_one_of_modEq_conductor χ a ha hmod⟩,
    χ.primitiveCharacter, fun n ↦ ?_⟩
  · rw [principalCharacter_apply]
    split_ifs with h
    · rw [mul_one, q27_apply_eq_primitiveCharacter χ n h]
    · rw [mul_zero]
      exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])

/-- DLMF 27.8.8: every character is `χ = χ₀ χ₁` with `χ₀` a character mod an induced modulus
`d` (here the conductor) and `χ₁` the principal character mod `k`. -/
@[dlmf 27.8.E8]
theorem DirichletCharacter.eq_mul_principal {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :
    IsInducedModulus χ χ.conductor ∧ ∃ χ₀ : DirichletCharacter ℂ χ.conductor,
      ∀ n : ℕ, χ n = χ₀ n * (1 : DirichletCharacter ℂ k) n :=
  q27_eq_mul_principal χ

/-- §27.8 after 27.8.8: for odd `k`, the real characters mod `k` are the principal character
and the quadratic characters `n ↦ (n|P) χ₁(n)`, `P ∣ k` (§27.9). -/
@[dlmf 27.8]
theorem real_character_eq_jacobiSym {k : ℕ} [NeZero k] (hk : Odd k)
    (χ : DirichletCharacter ℂ k) (hχ : ∀ n : ℕ, (χ n).im = 0) :
    ∃ P : ℕ, P ∣ k ∧ ∀ n : ℕ, χ n = (jacobiSym n P : ℂ) * (1 : DirichletCharacter ℂ k) n := by
  sorry

/-! ### §27.9 Quadratic characters -/

/-- §27.9: the Legendre symbol `(n|p)` for an odd prime `p` is `0` if `p ∣ n`, `1` if
`x² ≡ n (mod p)` is solvable and `p ∤ n`, `-1` otherwise (Mathlib's `legendreSym`). -/
@[dlmf 27.9]
theorem legendreSym_cases (p : ℕ) [Fact p.Prime] (n : ℤ) :
    ((n : ZMod p) = 0 → legendreSym p n = 0) ∧
      ((n : ZMod p) ≠ 0 → (legendreSym p n = 1 ↔ IsSquare (n : ZMod p))) ∧
      (legendreSym p n = -1 ↔ ¬ IsSquare (n : ZMod p)) :=
  ⟨fun h ↦ (legendreSym.eq_zero_iff p n).mpr h, fun h ↦ legendreSym.eq_one_iff p h,
    legendreSym.eq_neg_one_iff p⟩

/-- §27.9: `(n|p)` is a Dirichlet character mod `p`. -/
@[dlmf 27.9]
theorem isDirichletCharacterFn_legendreSym (p : ℕ) [Fact p.Prime] :
    IsDirichletCharacterFn p fun n ↦ (legendreSym p n : ℂ) := by
  refine ⟨by simp [legendreSym.at_one], fun m n _ _ ↦ ?_, fun n _ ↦ ?_, fun n _ hn ↦ ?_⟩
  · push_cast; rw [legendreSym.mul]; push_cast; ring
  · show (legendreSym p ((n + p : ℕ) : ℤ) : ℂ) = legendreSym p (n : ℤ)
    rw [legendreSym.mod p ((n + p : ℕ) : ℤ), legendreSym.mod p (n : ℤ)]
    push_cast
    rw [Int.add_emod_right]
  · have hp : p ∣ n := by
      have := Nat.gcd_dvd_right n p
      rcases (Nat.dvd_prime Fact.out).mp this with h | h
      · exact absurd h hn
      · exact h ▸ Nat.gcd_dvd_left n p
    have : ((n : ℤ) : ZMod p) = 0 := by
      push_cast; exact (ZMod.natCast_eq_zero_iff n p).mpr hp
    simp [(legendreSym.eq_zero_iff p n).mpr this]

/-- DLMF 27.9.1: `(-1|p) = (-1)^{(p-1)/2}` for an odd prime `p`. -/
@[dlmf 27.9.E1]
theorem legendreSym_neg_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-1) = (-1) ^ ((p - 1) / 2) := by
  rw [legendreSym.at_neg_one hp, ZMod.χ₄_eq_neg_one_pow
    ((Nat.Prime.eq_two_or_odd Fact.out).resolve_left hp)]
  have := (Nat.Prime.eq_two_or_odd (Fact.out : p.Prime)).resolve_left hp
  congr 1
  omega

/-- `(-1)^{(P²-1)/8} = χ₈(P)` for odd `P`. -/
theorem n27_neg_one_pow_eq_chi8 {P : ℕ} (hP : P % 2 = 1) :
    ((-1 : ℤ) ^ ((P ^ 2 - 1) / 8)) = ZMod.χ₈ P := by
  rw [ZMod.χ₈_nat_eq_if_mod_eight, neg_one_pow_eq_pow_mod_two, ← Nat.mod_mul_right_div_self]
  have hx : 1 ≤ P ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : (P ^ 2 - 1) % (8 * 2) = ((P % 16) ^ 2 % 16 + 15) % 16 := by
    rw [← Nat.pow_mod]; omega
  rw [h3, show P % 2 = P % 16 % 2 by omega, show P % 8 = P % 16 % 8 by omega]
  have hr : P % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hr2 : P % 16 % 2 = 1 := by omega
  generalize P % 16 = r at hr hr2 ⊢
  interval_cases r <;> simp_all

/-- DLMF 27.9.2: `(2|p) = (-1)^{(p²-1)/8}` for an odd prime `p`. -/
@[dlmf 27.9.E2]
theorem legendreSym_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p 2 = (-1) ^ ((p ^ 2 - 1) / 8) := by
  rw [legendreSym.at_two hp, n27_neg_one_pow_eq_chi8
    ((Nat.Prime.eq_two_or_odd Fact.out).resolve_left hp)]

/-- DLMF 27.9.3, the quadratic reciprocity law: `(p|q)(q|p) = (-1)^{(p-1)(q-1)/4}` for distinct
odd primes `p, q`. -/
@[dlmf 27.9.E3]
theorem legendreSym_reciprocity (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2)
    (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ ((p - 1) * (q - 1) / 4) := by
  rw [legendreSym.quadratic_reciprocity hp hq hpq]
  obtain ⟨a, rfl⟩ := (Nat.Prime.eq_two_or_odd' (Fact.out : p.Prime)).resolve_left hp
  obtain ⟨b, rfl⟩ := (Nat.Prime.eq_two_or_odd' (Fact.out : q.Prime)).resolve_left hq
  congr 1
  rw [show 2 * a + 1 - 1 = 2 * a by omega, show 2 * b + 1 - 1 = 2 * b by omega,
    show 2 * a * (2 * b) = 4 * (a * b) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  congr 1 <;> omega

/-- §27.9: the Jacobi symbol `(n|P)` for odd `P = ∏ p_r^{a_r}` is `∏ (n|p_r)^{a_r}`, with
`(n|1) = 1` (Mathlib's `jacobiSym`): it is `1` at `P = 1`, the Legendre symbol at primes, and
multiplicative in `P`. -/
@[dlmf 27.9]
theorem jacobiSym_cases (n : ℤ) :
    jacobiSym n 1 = 1 ∧ (∀ p : ℕ, (hp : p.Prime) → jacobiSym n p = @legendreSym p ⟨hp⟩ n) ∧
      ∀ P Q : ℕ, P ≠ 0 → Q ≠ 0 → jacobiSym n (P * Q) = jacobiSym n P * jacobiSym n Q :=
  ⟨jacobiSym.one_right n, fun p hp ↦ (@jacobiSym.legendreSym.to_jacobiSym p ⟨hp⟩ n).symm,
    fun _ _ hP hQ ↦ jacobiSym.mul_right' n hP hQ⟩

/-- §27.9: for odd `P`, `(n|P)` is a Dirichlet character mod `P`. -/
@[dlmf 27.9]
theorem isDirichletCharacterFn_jacobiSym {P : ℕ} (hP : Odd P) :
    IsDirichletCharacterFn P fun n ↦ (jacobiSym n P : ℂ) := by
  have hP0 : P ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hP)
  have : NeZero P := ⟨hP0⟩
  refine ⟨by simp [jacobiSym.one_left], fun m n _ _ ↦ ?_, fun n _ ↦ ?_, fun n _ hn ↦ ?_⟩
  · push_cast; rw [jacobiSym.mul_left]; push_cast; ring
  · show (jacobiSym ((n + P : ℕ) : ℤ) P : ℂ) = (jacobiSym (n : ℤ) P : ℂ)
    rw [jacobiSym.mod_left' (a₁ := ((n + P : ℕ) : ℤ)) (a₂ := (n : ℤ))
      (by push_cast; exact Int.add_emod_right _ _)]
  · have : jacobiSym n P = 0 := jacobiSym.eq_zero_iff_not_coprime.mpr (by
      rw [Int.gcd_natCast_natCast]; exact hn)
    simp [this]

/-- §27.9: 27.9.1 holds for the Jacobi symbol, `(-1|P) = (-1)^{(P-1)/2}`, `P` odd. -/
@[dlmf 27.9.E1]
theorem jacobiSym_neg_one {P : ℕ} (hP : Odd P) : jacobiSym (-1) P = (-1) ^ ((P - 1) / 2) := by
  rw [jacobiSym.at_neg_one hP, ZMod.χ₄_eq_neg_one_pow (Nat.odd_iff.mp hP)]
  congr 1
  have := Nat.odd_iff.mp hP
  omega

/-- §27.9: 27.9.2 holds for the Jacobi symbol, `(2|P) = (-1)^{(P²-1)/8}`, `P` odd. -/
@[dlmf 27.9.E2]
theorem jacobiSym_two {P : ℕ} (hP : Odd P) : jacobiSym 2 P = (-1) ^ ((P ^ 2 - 1) / 8) := by
  rw [jacobiSym.at_two hP, n27_neg_one_pow_eq_chi8 (Nat.odd_iff.mp hP)]

/-- §27.9: 27.9.3 holds for relatively prime odd `P, Q`:
`(P|Q)(Q|P) = (-1)^{(P-1)(Q-1)/4}`. -/
@[dlmf 27.9.E3]
theorem jacobiSym_reciprocity {P Q : ℕ} (hP : Odd P) (hQ : Odd Q) (hPQ : P.Coprime Q) :
    jacobiSym P Q * jacobiSym Q P = (-1) ^ ((P - 1) * (Q - 1) / 4) := by
  rw [jacobiSym.quadratic_reciprocity hP hQ, mul_assoc, ← sq,
    jacobiSym.sq_one (by rw [Int.gcd_natCast_natCast]; exact hPQ.symm), mul_one]
  obtain ⟨a, rfl⟩ := hP
  obtain ⟨b, rfl⟩ := hQ
  congr 1
  rw [show 2 * a + 1 - 1 = 2 * a by omega, show 2 * b + 1 - 1 = 2 * b by omega,
    show 2 * a * (2 * b) = 4 * (a * b) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  congr 1 <;> omega

/-! ### §27.10 Periodic number-theoretic functions -/

/-- DLMF 27.10.1: `f` is periodic mod `k` if `f(n + k) = f(n)`, `n = 1, 2, …`. -/
@[dlmf 27.10.E1]
def IsPeriodicFn {α : Type*} (k : ℕ) (f : ℕ → α) : Prop :=
  ∀ n : ℕ, 0 < n → f (n + k) = f n

/-- §27.10 after 27.10.1: the Dirichlet characters mod `k` and `n ↦ (n, k)` are periodic
mod `k`. -/
@[dlmf 27.10.E1]
theorem isPeriodicFn_examples {k : ℕ} (χ : DirichletCharacter ℂ k) :
    IsPeriodicFn k (fun n ↦ χ n) ∧ IsPeriodicFn k (fun n ↦ n.gcd k) :=
  ⟨χ.isDirichletCharacterFn.2.2.1, fun n _ ↦ Nat.gcd_add_self_left k n⟩

/-- The exponential `e^{2πi m n/k}` of §27.10. -/
def expFrac (m n k : ℕ) : ℂ := Complex.exp (2 * π * I * m * n / k)

/-- DLMF 27.10.3: the finite Fourier coefficients `g(m) = k⁻¹ ∑_{n=1}^k f(n) e^{-2πimn/k}`. -/
@[dlmf 27.10.E3]
def finiteFourierCoeff (k : ℕ) (f : ℕ → ℂ) (m : ℕ) : ℂ :=
  (k : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 k, f n * Complex.exp (-(2 * π * I * m * n / k))

/-- `∑_{m=1}^k g(m) = ∑_{a ∈ ℤ/k} g(a)`. -/
theorem q27_sum_Icc_eq_sum_zmod {M : Type*} [AddCommMonoid M] {k : ℕ} [NeZero k]
    (g : ZMod k → M) : ∑ m ∈ Icc 1 k, g m = ∑ a : ZMod k, g a := by
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  refine sum_nbij' (fun m ↦ (m : ZMod k)) (fun a ↦ if a = 0 then k else a.val) ?_ ?_ ?_ ?_ ?_
  · intro m _; exact mem_univ _
  · intro a _
    rw [mem_Icc]
    split_ifs with h
    · exact ⟨hk, le_rfl⟩
    · exact ⟨Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).mpr h), (ZMod.val_lt a).le⟩
  · intro m hm
    rw [mem_Icc] at hm
    split_ifs with h
    · rw [ZMod.natCast_eq_zero_iff] at h
      exact le_antisymm (Nat.le_of_dvd (by omega) h) hm.2
    · rw [ZMod.val_natCast]
      apply Nat.mod_eq_of_lt
      rcases hm.2.lt_or_eq with h' | h'
      · exact h'
      · exact absurd (by rw [h', ZMod.natCast_self]) h
  · intro a _
    split_ifs with h
    · rw [h, ZMod.natCast_self]
    · exact ZMod.natCast_zmod_val a
  · intro m _; rfl

/-- Group `1 ≤ m ≤ n` by `e = n/(m, n)`: `m = (n/e) r` with `1 ≤ r ≤ e`, `(r, e) = 1`. -/
theorem q27_sum_Icc_eq_sum_divisors_coprime {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : ℕ → M) :
    ∑ m ∈ Icc 1 n, F m =
      ∑ e ∈ n.divisors, ∑ r ∈ (Icc 1 e).filter (fun r ↦ r.Coprime e), F (n / e * r) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← sum_fiberwise_of_maps_to (g := fun m ↦ n / Nat.gcd m n) (t := n.divisors)
    (s := Icc 1 n) (f := F)]
  · refine sum_congr rfl fun e he ↦ ?_
    obtain ⟨c, hc⟩ := Nat.dvd_of_mem_divisors he
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h, mul_zero] at hc; omega
      · exact h
    have hne : n / e = c := by rw [hc, Nat.mul_div_cancel_left _ he0]
    have hg : ∀ m, n / Nat.gcd m n = e → Nat.gcd m n = c := by
      intro m hm
      obtain ⟨t, ht⟩ := Nat.gcd_dvd_right m n
      have hg0 := Nat.gcd_pos_of_pos_right m hn
      set g := Nat.gcd m n
      rw [ht, Nat.mul_div_cancel_left _ hg0] at hm
      rw [hm] at ht
      rw [ht, mul_comm] at hc
      exact Nat.eq_of_mul_eq_mul_left he0 hc
    rw [hne]
    symm
    refine sum_nbij' (fun r ↦ c * r) (fun m ↦ m / c) ?_ ?_ ?_ ?_ ?_
    · intro r hr
      rw [mem_filter, mem_Icc] at hr
      rw [mem_filter, mem_Icc]
      refine ⟨⟨by nlinarith, ?_⟩, ?_⟩
      · rw [hc, mul_comm e c]; exact Nat.mul_le_mul_left c hr.1.2
      · rw [hc, mul_comm e c, Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hr.2, mul_one,
          Nat.mul_div_cancel_left _ hc0]
    · intro m hm
      rw [mem_filter, mem_Icc] at hm
      have hgc := hg m hm.2
      have hcm : c ∣ m := hgc ▸ Nat.gcd_dvd_left m n
      obtain ⟨t, rfl⟩ := hcm
      rw [mem_filter, mem_Icc, Nat.mul_div_cancel_left _ hc0]
      have ht0 : 0 < t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · rw [h, mul_zero] at hm; omega
        · exact h
      refine ⟨⟨ht0, ?_⟩, ?_⟩
      · rw [hc, mul_comm e c] at hm
        exact Nat.le_of_mul_le_mul_left hm.1.2 hc0
      · rw [hc, mul_comm e c, Nat.gcd_mul_left] at hgc
        exact Nat.eq_of_mul_eq_mul_left hc0 (hgc.trans (mul_one c).symm)
    · intro r _
      exact Nat.mul_div_cancel_left _ hc0
    · intro m hm
      rw [mem_filter] at hm
      exact Nat.mul_div_cancel' ((hg m hm.2) ▸ Nat.gcd_dvd_left m n)
    · intro r _
      rfl
  · intro m _
    rw [Nat.mem_divisors]
    exact ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _), hn.ne'⟩

/-- `∑_{m=1}^k e^{2πimn/k} = k` if `k ∣ n` and `0` otherwise. -/
theorem q27_sum_expFrac {k : ℕ} (hk : 0 < k) (n : ℕ) :
    ∑ m ∈ Icc 1 k, expFrac m n k = if k ∣ n then (k : ℂ) else 0 := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  set w := Complex.exp (2 * π * I * n / k) with hw
  have hterm : ∀ m : ℕ, expFrac m n k = w ^ m := by
    intro m
    rw [expFrac, hw, ← Complex.exp_nat_mul]
    congr 1; ring
  have hwk : w ^ k = 1 := by
    rw [← hterm, expFrac, show (2 * π * I * (k : ℕ) * n / k : ℂ) = (n : ℂ) * (2 * π * I) by
      field_simp]
    exact Complex.exp_nat_mul_two_pi_mul_I n
  simp_rw [hterm]
  have hshift : ∑ m ∈ Icc 1 k, w ^ m = w * ∑ j ∈ range k, w ^ j := by
    rw [mul_sum]
    rw [show Icc 1 k = (range k).map ⟨(· + 1), add_left_injective 1⟩ by
      ext m; simp only [mem_Icc, mem_map, mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro h; exact ⟨m - 1, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩; omega]
    rw [sum_map]
    exact sum_congr rfl fun j _ ↦ by simp [pow_succ']
  split_ifs with h
  · obtain ⟨t, rfl⟩ := h
    have hw1 : w = 1 := by
      rw [hw, show (2 * π * I * ((k * t : ℕ) : ℂ) / k : ℂ) = (t : ℂ) * (2 * π * I) by
        push_cast; field_simp]
      exact Complex.exp_nat_mul_two_pi_mul_I t
    simp [hw1]
  · have hw1 : w ≠ 1 := by
      intro hw1
      apply h
      have hprim := Complex.isPrimitiveRoot_exp k hk.ne'
      rw [← hprim.pow_eq_one_iff_dvd]
      rw [← hw1, hw, ← Complex.exp_nat_mul]
      congr 1; ring
    rw [hshift, geom_sum_eq hw1, hwk, sub_self, zero_div, mul_zero]

/-- `f(n + kq) = f(n)` for `f` periodic mod `k`. -/
theorem q27_isPeriodicFn_add_mul {α : Type*} {k : ℕ} {f : ℕ → α} (hf : IsPeriodicFn k f)
    {n : ℕ} (hn : 0 < n) (q : ℕ) : f (n + k * q) = f n := by
  induction q with
  | zero => simp
  | succ q ih => rw [mul_add, mul_one, ← add_assoc, hf _ (by omega), ih]

/-- `e^{-2πimj/k} = e^{2πim(k-j)/k}` for `j ≤ k`. -/
theorem q27_exp_neg_eq {k : ℕ} (hk : 0 < k) (m j : ℕ) (hj : j ≤ k) :
    Complex.exp (-(2 * π * I * m * j / k)) = expFrac m (k - j) k := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [expFrac, Nat.cast_sub hj, show (2 * π * I * m * ((k : ℂ) - j) / k) =
    -(2 * π * I * m * j / k) + (m : ℂ) * (2 * π * I) by field_simp; ring, Complex.exp_add,
    Complex.exp_nat_mul_two_pi_mul_I, mul_one]

/-- `e(ma/k) e(mb/k) = e(m(a+b)/k)`. -/
theorem q27_expFrac_mul (m a b k : ℕ) : expFrac m a k * expFrac m b k = expFrac m (a + b) k := by
  rw [expFrac, expFrac, expFrac, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `e(mn/k) = e(nm/k)`. -/
theorem q27_expFrac_comm (m n k : ℕ) : expFrac m n k = expFrac n m k := by
  rw [expFrac, expFrac]; congr 1; ring

/-- DLMF 27.10.2–27.10.3 (proof). -/
theorem q27_finiteFourier_expansion {k : ℕ} (hk : 0 < k) {f : ℕ → ℂ} (hf : IsPeriodicFn k f) :
    (∀ n : ℕ, 0 < n → f n = ∑ m ∈ Finset.Icc 1 k, finiteFourierCoeff k f m * expFrac m n k) ∧
      IsPeriodicFn k (finiteFourierCoeff k f) := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun n hn ↦ ?_, fun m _ ↦ ?_⟩
  · simp only [finiteFourierCoeff]
    have e1 : ∀ m ∈ Icc 1 k, (k : ℂ)⁻¹ * (∑ j ∈ Icc 1 k, f j *
        Complex.exp (-(2 * π * I * m * j / k))) * expFrac m n k =
        (k : ℂ)⁻¹ * ∑ j ∈ Icc 1 k, f j * expFrac m (n + (k - j)) k := by
      intro m _
      rw [mul_assoc, sum_mul]
      congr 1
      refine sum_congr rfl fun j hj ↦ ?_
      rw [q27_exp_neg_eq hk m j (mem_Icc.mp hj).2, mul_assoc, mul_comm (expFrac _ (k - j) _),
        q27_expFrac_mul]
    rw [sum_congr rfl e1, ← mul_sum, sum_comm]
    simp_rw [← mul_sum]
    have e2 : ∀ j ∈ Icc 1 k, f j * ∑ m ∈ Icc 1 k, expFrac m (n + (k - j)) k =
        f j * if k ∣ n + (k - j) then (k : ℂ) else 0 := by
      intro j _
      rw [q27_sum_expFrac hk]
    rw [sum_congr rfl e2]
    set j₀ := (n - 1) % k + 1 with hj₀
    obtain ⟨q, hq⟩ : ∃ q, n = j₀ + k * q :=
      ⟨(n - 1) / k, by have := Nat.div_add_mod (n - 1) k; rw [hj₀]; omega⟩
    have hj₀k : j₀ ∈ Icc 1 k := by
      rw [mem_Icc, hj₀]; exact ⟨by omega, Nat.mod_lt _ hk⟩
    have hdiv : ∀ j ∈ Icc 1 k, (k ∣ n + (k - j) ↔ j = j₀) := by
      intro j hj
      rw [mem_Icc] at hj hj₀k
      constructor
      · rintro ⟨t, ht⟩
        rcases Nat.lt_or_ge t (q + 1) with h | h
        · have : k * t ≤ k * q := Nat.mul_le_mul_left k (by omega)
          omega
        · rcases h.lt_or_eq with h' | h'
          · have : k * (q + 2) ≤ k * t := Nat.mul_le_mul_left k (by omega)
            have e : k * (q + 2) = k * q + 2 * k := by ring
            omega
          · rw [← h', mul_add, mul_one] at ht
            omega
      · rintro rfl
        exact ⟨q + 1, by rw [mul_add, mul_one]; omega⟩
    rw [sum_eq_single_of_mem j₀ hj₀k]
    · rw [ite_eq_left ((hdiv j₀ hj₀k).mpr rfl), hq, q27_isPeriodicFn_add_mul hf (by omega) q]
      field_simp
    · intro j hj hne
      rw [ite_eq_right (fun h ↦ hne ((hdiv j hj).mp h)), mul_zero]
  · simp only [finiteFourierCoeff]
    congr 1
    refine sum_congr rfl fun j hj ↦ ?_
    have hjk := (mem_Icc.mp hj).2
    rw [q27_exp_neg_eq hk _ j hjk, q27_exp_neg_eq hk _ j hjk]
    congr 1
    rw [q27_expFrac_comm, ← q27_expFrac_mul, q27_expFrac_comm _ m]
    have : expFrac (k - j) k k = 1 := by
      rw [expFrac, show (2 * π * I * ((k - j : ℕ) : ℂ) * k / k) = ((k - j : ℕ) : ℂ) * (2 * π * I) by
        field_simp]
      exact Complex.exp_nat_mul_two_pi_mul_I _
    rw [this, mul_one]

/-- DLMF 27.10.2–27.10.3: a function periodic mod `k ≥ 1` is the finite Fourier series
`f(n) = ∑_{m=1}^k g(m) e^{2πimn/k}` with the coefficients 27.10.3, which are periodic mod `k`. -/
@[dlmf 27.10.E2, dlmf 27.10.E3]
theorem finiteFourier_expansion {k : ℕ} (hk : 0 < k) {f : ℕ → ℂ} (hf : IsPeriodicFn k f) :
    (∀ n : ℕ, 0 < n → f n = ∑ m ∈ Finset.Icc 1 k, finiteFourierCoeff k f m * expFrac m n k) ∧
      IsPeriodicFn k (finiteFourierCoeff k f) := by
  exact q27_finiteFourier_expansion hk hf

/-- DLMF 27.10.4: Ramanujan's sum `c_k(n) = ∑_{m=1}^k χ₁(m) e^{2πimn/k}`, the sum over
`1 ≤ m ≤ k` with `(m, k) = 1`. -/
@[dlmf 27.10.E4]
def ramanujanSum (k n : ℕ) : ℂ :=
  ∑ m ∈ (Finset.Icc 1 k).filter (fun m ↦ m.Coprime k), expFrac m n k

/-- `c_k(n)` as a power sum over primitive roots (proof). -/
theorem q27_ramanujanSum_eq_sum_primitiveRoots {k : ℕ} (hk : 0 < k) (n : ℕ) :
    ramanujanSum k n = ∑ ζ ∈ primitiveRoots k ℂ, ζ ^ n := by
  have : NeZero k := ⟨hk.ne'⟩
  set ζ := Complex.exp (2 * π * I / k) with hζ
  have hprim : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk.ne'
  have hpow : ∀ m : ℕ, ζ ^ m = Complex.exp (2 * π * I * m / k) := by
    intro m
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1; ring
  have hlt : ∀ m ∈ (Icc 1 k).filter (fun m ↦ m.Coprime k), 1 < k → m < k := by
    intro m hm hk1
    rw [mem_filter, mem_Icc] at hm
    rcases hm.1.2.lt_or_eq with h | h
    · exact h
    · rw [h, Nat.coprime_self] at hm; omega
  rw [ramanujanSum]
  refine sum_bij (fun m _ ↦ ζ ^ m) ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_filter] at hm
    rw [mem_primitiveRoots hk]
    exact (hprim.pow_iff_coprime hk m).mpr hm.2
  · intro m₁ hm₁ m₂ hm₂ h
    rcases Nat.lt_or_ge 1 k with hk1 | hk1
    · exact hprim.pow_inj (hlt m₁ hm₁ hk1) (hlt m₂ hm₂ hk1) h
    · rw [mem_filter, mem_Icc] at hm₁ hm₂; omega
  · intro η hη
    rw [mem_primitiveRoots hk] at hη
    obtain ⟨i, hik, hi⟩ := hprim.eq_pow_of_pow_eq_one hη.pow_eq_one
    have hcop : i.Coprime k := (hprim.pow_iff_coprime hk i).mp (hi ▸ hη)
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have hk1 : k = 1 := by rwa [Nat.coprime_zero_left] at hcop
      refine ⟨1, ?_, ?_⟩
      · rw [mem_filter, mem_Icc]; exact ⟨⟨le_rfl, by omega⟩, Nat.coprime_one_left k⟩
      · rw [← hi, pow_zero, pow_one]
        have := hprim.pow_eq_one
        rwa [hk1, pow_one] at this
    · exact ⟨i, by rw [mem_filter, mem_Icc]; exact ⟨⟨hi0, hik.le⟩, hcop⟩, hi⟩
  · intro m _
    rw [expFrac, ← pow_mul, hpow]
    congr 1
    push_cast; ring

/-- DLMF 27.10.5 (proof, by Möbius inversion). -/
theorem q27_ramanujanSum_eq_sum_divisors {k : ℕ} (hk : 0 < k) (n : ℕ) :
    ramanujanSum k n = ∑ d ∈ (n.gcd k).divisors, (d : ℂ) * μ (k / d) := by
  have hS : ∀ K > 0, ∑ d ∈ K.divisors, ramanujanSum d n =
      (fun K ↦ if K ∣ n then (K : ℂ) else 0) K := by
    intro K hK
    simp only
    rw [← q27_sum_expFrac hK n, q27_sum_Icc_eq_sum_divisors_coprime K]
    refine sum_congr rfl fun e he ↦ ?_
    rw [ramanujanSum]
    refine sum_congr rfl fun r _ ↦ ?_
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    obtain ⟨c, hc⟩ := Nat.dvd_of_mem_divisors he
    have hc0 : (c : ℂ) ≠ 0 := by
      have : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; omega
      exact_mod_cast this
    have he0' : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
    rw [hc, Nat.mul_div_cancel_left _ he0, expFrac, expFrac]
    congr 1
    push_cast
    field_simp
  have h := (sum_eq_iff_sum_mul_moebius_eq (R := ℂ)).mp hS k hk
  rw [← h, Nat.sum_divisorsAntidiagonal' (fun a b ↦ (μ a : ℂ) *
    (if b ∣ n then (b : ℂ) else 0))]
  simp_rw [mul_ite, mul_zero]
  rw [← sum_filter]
  have hfil : k.divisors.filter (fun d ↦ d ∣ n) = (n.gcd k).divisors := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h3, h1⟩, (Nat.gcd_pos_of_pos_right n hk).ne'⟩
    · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h2, hk.ne'⟩, h1⟩
  rw [hfil]
  exact sum_congr rfl fun d _ ↦ mul_comm _ _

/-- §27.10 after 27.10.4: `c_k(n)` is the sum of the `n`th powers of the primitive `k`th roots
of unity. -/
@[dlmf 27.10.E4]
theorem ramanujanSum_eq_sum_primitiveRoots {k : ℕ} (hk : 0 < k) (n : ℕ) :
    ramanujanSum k n = ∑ ζ ∈ primitiveRoots k ℂ, ζ ^ n := by
  exact q27_ramanujanSum_eq_sum_primitiveRoots hk n

/-- DLMF 27.10.5: `c_k(n) = ∑_{d∣(n,k)} d μ(k/d)`. -/
@[dlmf 27.10.E5]
theorem ramanujanSum_eq_sum_divisors {k : ℕ} (hk : 0 < k) (n : ℕ) :
    ramanujanSum k n = ∑ d ∈ (n.gcd k).divisors, (d : ℂ) * μ (k / d) := by
  exact q27_ramanujanSum_eq_sum_divisors hk n

/-- DLMF 27.10.6: `s_k(n) = ∑_{d∣(n,k)} f(d) g(k/d)`. -/
@[dlmf 27.10.E6]
def divisorConvolutionSum (f g : ℕ → ℂ) (k n : ℕ) : ℂ :=
  ∑ d ∈ (n.gcd k).divisors, f d * g (k / d)

/-- §27.10 after 27.10.6: `s_k(n)` is periodic in `n` mod `k`. -/
@[dlmf 27.10.E6]
theorem isPeriodicFn_divisorConvolutionSum (f g : ℕ → ℂ) (k : ℕ) :
    IsPeriodicFn k (divisorConvolutionSum f g k) := by
  intro n _
  simp only [divisorConvolutionSum, Nat.gcd_add_self_left]

/-- DLMF 27.10.7–27.10.8: `s_k(n) = ∑_{m=1}^k a_k(m) e^{2πimn/k}` with
`a_k(m) = ∑_{d∣(m,k)} g(d) f(k/d) d/k`. -/
@[dlmf 27.10.E7, dlmf 27.10.E8]
theorem divisorConvolutionSum_fourier (f g : ℕ → ℂ) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    divisorConvolutionSum f g k n = ∑ m ∈ Finset.Icc 1 k,
      (∑ d ∈ (m.gcd k).divisors, g d * f (k / d) * d / k) * expFrac m n k := by
  -- swap the order of summation
  have hswap : ∑ m ∈ Finset.Icc 1 k, (∑ d ∈ (m.gcd k).divisors, g d * f (k / d) * d / k) *
      expFrac m n k = ∑ d ∈ k.divisors, ∑ m ∈ (Icc 1 k).filter (d ∣ ·),
        g d * f (k / d) * d / k * expFrac m n k := by
    simp_rw [sum_mul]
    refine sum_comm' fun m d ↦ ?_
    simp only [mem_Icc, Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨hm, ⟨hdm, hdk⟩, _⟩; exact ⟨⟨hm, hdm⟩, hdk, hk.ne'⟩
    · rintro ⟨⟨hm, hdm⟩, hdk, _⟩
      exact ⟨hm, ⟨hdm, hdk⟩, Nat.gcd_ne_zero_right hk.ne'⟩
  rw [hswap]
  -- inner sums
  have hinner : ∀ d ∈ k.divisors, ∑ m ∈ (Icc 1 k).filter (d ∣ ·),
      g d * f (k / d) * d / k * expFrac m n k =
        if (k / d) ∣ n then g d * f (k / d) else 0 := by
    intro d hd
    have hdk := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    obtain ⟨e, he⟩ := hdk
    have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; rw [mul_zero] at he; omega)
    have hke : k / d = e := by rw [he, Nat.mul_div_cancel_left _ hd0]
    rw [← mul_sum, hke]
    have hre : ∑ m ∈ (Icc 1 k).filter (d ∣ ·), expFrac m n k = ∑ j ∈ Icc 1 e, expFrac j n e := by
      refine sum_nbij' (fun m ↦ m / d) (fun j ↦ d * j) ?_ ?_ ?_ ?_ ?_
      · intro m hm
        simp only [mem_filter, mem_Icc] at hm ⊢
        obtain ⟨⟨h1, h2⟩, t, rfl⟩ := hm
        rw [Nat.mul_div_cancel_left _ hd0]
        refine ⟨by rcases Nat.eq_zero_or_pos t with h | h <;> [simp [h] at h1; exact h], ?_⟩
        rw [he] at h2; exact Nat.le_of_mul_le_mul_left h2 hd0
      · intro j hj
        simp only [mem_filter, mem_Icc] at hj ⊢
        refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right d j⟩
        rw [he]; exact Nat.mul_le_mul_left d hj.2
      · intro m hm
        simp only [mem_filter] at hm
        exact Nat.mul_div_cancel' hm.2
      · intro j _; exact Nat.mul_div_cancel_left _ hd0
      · intro m hm
        simp only [mem_filter] at hm
        obtain ⟨t, rfl⟩ := hm.2
        rw [Nat.mul_div_cancel_left _ hd0, expFrac, expFrac, he]
        congr 1
        have : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
        push_cast
        field_simp
    rw [hre, q27_sum_expFrac he0]
    have hk' : (k : ℂ) = d * e := by rw [he]; push_cast; ring
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
    split_ifs
    · rw [hk']; field_simp
    · simp
  rw [sum_congr rfl hinner, ← sum_filter, divisorConvolutionSum]
  -- reindex `d ↦ k / d`
  refine sum_nbij' (fun e ↦ k / e) (fun d ↦ k / d) ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [Nat.mem_divisors, Nat.dvd_gcd_iff] at he
    simp only [mem_filter, Nat.mem_divisors]
    refine ⟨⟨Nat.div_dvd_of_dvd he.1.2, hk.ne'⟩, ?_⟩
    rw [Nat.div_div_self he.1.2 hk.ne']; exact he.1.1
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    simp only [Nat.mem_divisors, Nat.dvd_gcd_iff]
    exact ⟨⟨hd.2, Nat.div_dvd_of_dvd hd.1.1⟩, Nat.gcd_ne_zero_right hk.ne'⟩
  · intro e he
    simp only [Nat.mem_divisors, Nat.dvd_gcd_iff] at he
    exact Nat.div_div_self he.1.2 hk.ne'
  · intro d hd
    simp only [mem_filter, Nat.mem_divisors] at hd
    exact Nat.div_div_self hd.1.1 hk.ne'
  · intro e he
    simp only [Nat.mem_divisors, Nat.dvd_gcd_iff] at he
    rw [Nat.div_div_self he.1.2 hk.ne', mul_comm]

/-- DLMF 27.10.9: the Gauss sum `G(n, χ) = ∑_{m=1}^k χ(m) e^{2πimn/k}`. -/
@[dlmf 27.10.E9]
def gaussSumDLMF {k : ℕ} (χ : DirichletCharacter ℂ k) (n : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 k, χ m * expFrac m n k

/-- §27.10 after 27.10.9: `G(n, χ₁) = c_k(n)`. -/
@[dlmf 27.10.E9]
theorem gaussSumDLMF_one (k n : ℕ) : gaussSumDLMF (1 : DirichletCharacter ℂ k) n =
    ramanujanSum k n := by
  rw [gaussSumDLMF, ramanujanSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [principalCharacter_apply]
  split_ifs <;> simp

/-- DLMF 27.10.9 bridge to Mathlib (proof). -/
theorem q27_gaussSumDLMF_eq_gaussSum {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (n : ℕ) :
    gaussSumDLMF χ n = gaussSum χ ((ZMod.stdAddChar (N := k)).mulShift (n : ZMod k)) := by
  rw [gaussSumDLMF, gaussSum, ← q27_sum_Icc_eq_sum_zmod]
  refine sum_congr rfl fun m _ ↦ ?_
  have h := ZMod.stdAddChar_coe (N := k) ((n * m : ℕ) : ℤ)
  rw [Int.cast_natCast] at h
  rw [AddChar.mulShift_apply, ← Nat.cast_mul, h, expFrac]
  congr 2
  push_cast
  ring

/-- DLMF's `G(n, χ)` is Mathlib's `gaussSum χ (ψ.mulShift n)` with the standard additive
character `ψ = ZMod.stdAddChar` of `ZMod k`. -/
@[dlmf 27.10.E9]
theorem gaussSumDLMF_eq_gaussSum {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (n : ℕ) :
    gaussSumDLMF χ n = gaussSum χ ((ZMod.stdAddChar (N := k)).mulShift (n : ZMod k)) := by
  exact q27_gaussSumDLMF_eq_gaussSum χ n

/-- DLMF 27.10.10: `G(n, χ)` is separable for `n` if `G(n, χ) = χ̄(n) G(1, χ)`. -/
@[dlmf 27.10.E10]
def GaussSumSeparable {k : ℕ} (χ : DirichletCharacter ℂ k) (n : ℕ) : Prop :=
  gaussSumDLMF χ n = starRingEnd ℂ (χ n) * gaussSumDLMF χ 1

/-- Separability of Gauss sums (proof). -/
theorem q27_gaussSumSeparable_iff {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :
    (∀ n : ℕ, n.Coprime k → GaussSumSeparable χ n) ∧
      ((∀ n, GaussSumSeparable χ n) ↔ ∀ n : ℕ, n.gcd k ≠ 1 → gaussSumDLMF χ n = 0) := by
  have h1 : ∀ n : ℕ, n.Coprime k → GaussSumSeparable χ n := by
    intro n hn
    obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime n k).mpr hn
    rw [GaussSumSeparable, q27_gaussSumDLMF_eq_gaussSum, q27_gaussSumDLMF_eq_gaussSum,
      Nat.cast_one, AddChar.mulShift_one, ← hu, gaussSum_mulShift_eq]
    congr 1
    exact (MulChar.star_apply' χ _).symm
  have h0 : ∀ n : ℕ, n.gcd k ≠ 1 → χ n = 0 := fun n hn ↦
    MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
  refine ⟨h1, fun h n hn ↦ ?_, fun h n ↦ ?_⟩
  · rw [h n, h0 n hn, _root_.map_zero, zero_mul]
  · by_cases hn : n.Coprime k
    · exact h1 n hn
    · rw [GaussSumSeparable, h n hn, h0 n hn, _root_.map_zero, zero_mul]

/-- §27.10 after 27.10.10: `G(n, χ)` is separable for `(n, k) = 1`, and it is separable for
every `n` iff `G(n, χ) = 0` whenever `(n, k) > 1`. -/
@[dlmf 27.10.E10]
theorem gaussSumSeparable_iff {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) :
    (∀ n : ℕ, n.Coprime k → GaussSumSeparable χ n) ∧
      ((∀ n, GaussSumSeparable χ n) ↔ ∀ n : ℕ, n.gcd k ≠ 1 → gaussSumDLMF χ n = 0) := by
  exact q27_gaussSumSeparable_iff χ

/-- For primitive `χ`, `G(n, χ) = χ̄(n) G(1, χ)` in Mathlib's normalization. -/
theorem r27_gaussSum_mulShift {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}
    (hχ : χ.IsPrimitive) (a : ZMod k) :
    gaussSum χ ((ZMod.stdAddChar (N := k)).mulShift a) =
      starRingEnd ℂ (χ a) * gaussSum χ (ZMod.stdAddChar (N := k)) := by
  rw [gaussSum_mulShift_of_isPrimitive _ hχ a, ← MulChar.star_apply', Complex.star_def]

/-- `|G(1, χ)|² = k` for a primitive character `χ` mod `k`. -/
theorem r27_gaussSum_mul_conj {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}
    (hχ : χ.IsPrimitive) :
    gaussSum χ (ZMod.stdAddChar (N := k)) * starRingEnd ℂ (gaussSum χ (ZMod.stdAddChar (N := k)))
      = k := by
  set ψ := ZMod.stdAddChar (N := k)
  set G := gaussSum χ ψ
  have hR : 0 < ringChar (ZMod k) := by
    rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne k)
  have hψ : ψ.IsPrimitive := ZMod.isPrimitive_stdAddChar k
  set U : ℂ := ∑ a : ZMod k, χ a * starRingEnd ℂ (χ a)
  have hU : U ≠ 0 := by
    have hUr : U = ((∑ a : ZMod k, Complex.normSq (χ a) : ℝ) : ℂ) := by
      simp only [U, Complex.mul_conj, Complex.ofReal_sum]
    rw [hUr, Complex.ofReal_ne_zero]
    refine ne_of_gt (lt_of_lt_of_le ?_ (single_le_sum (f := fun a ↦ Complex.normSq (χ a))
      (fun a _ ↦ Complex.normSq_nonneg _) (mem_univ 1)))
    simp
  have hA : ∑ a : ZMod k, gaussSum χ (ψ.mulShift a) * starRingEnd ℂ (gaussSum χ (ψ.mulShift a))
      = U * (G * starRingEnd ℂ G) := by
    rw [Finset.sum_mul]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [r27_gaussSum_mulShift hχ a, map_mul, Complex.conj_conj]
    ring
  have hB : ∑ a : ZMod k, gaussSum χ (ψ.mulShift a) * starRingEnd ℂ (gaussSum χ (ψ.mulShift a))
      = k * U := by
    simp only [gaussSum, AddChar.mulShift_apply, map_sum, map_mul, AddChar.starComp_apply hR,
      AddChar.inv_apply, sum_mul, mul_sum]
    rw [sum_comm]
    simp only [U, mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [sum_comm]
    have : ∀ y : ZMod k, ∑ a : ZMod k, χ y * ψ (a * y) * (starRingEnd ℂ (χ x) * ψ (-(a * x))) =
        χ y * starRingEnd ℂ (χ x) * (if y - x = 0 then (k : ℂ) else 0) := by
      intro y
      have h := AddChar.sum_mulShift (y - x) hψ
      rw [ZMod.card] at h
      have h' : ∑ a : ZMod k, ψ (a * (y - x)) = if y - x = 0 then (k : ℂ) else 0 := by
        rw [h]; split_ifs <;> simp
      rw [← h', mul_sum]
      refine sum_congr rfl fun a _ ↦ ?_
      rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    simp_rw [this, sub_eq_zero, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    ring
  have h := hA.symm.trans hB
  rw [mul_comm (k : ℂ)] at h
  exact mul_left_cancel₀ hU h

/-- DLMF 27.10.11: for a primitive character `χ (mod k)`, `G(n, χ)` is separable for every
`n` and `|G(1, χ)|² = k`. -/
@[dlmf 27.10.E11]
theorem gaussSumDLMF_primitive {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}
    (hχ : χ.IsPrimitive) :
    (∀ n, GaussSumSeparable χ n) ∧ ‖gaussSumDLMF χ 1‖ ^ 2 = k := by
  have h1 : gaussSumDLMF χ 1 = gaussSum χ (ZMod.stdAddChar (N := k)) := by
    rw [gaussSumDLMF_eq_gaussSum, Nat.cast_one, AddChar.mulShift_one]
  refine ⟨fun n ↦ ?_, ?_⟩
  · rw [GaussSumSeparable, gaussSumDLMF_eq_gaussSum, r27_gaussSum_mulShift hχ, h1]
  · have h := r27_gaussSum_mul_conj hχ
    rw [← h1, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
    exact_mod_cast h

/-- A character sum over `ZMod N` is a sum over the units. -/
theorem s27_sum_char_eq_sum_units {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (e : ZMod N → ℂ) :
    ∑ a : ZMod N, χ a * e a = ∑ u : (ZMod N)ˣ, χ u * e u := by
  classical
  have : ∑ u : (ZMod N)ˣ, χ u * e u =
      ∑ a ∈ (univ : Finset (ZMod N)ˣ).map ⟨Units.val, Units.val_injective⟩, χ a * e a := by
    rw [sum_map]; rfl
  rw [this]
  refine (sum_subset (subset_univ _) fun a _ ha ↦ ?_).symm
  have : ¬IsUnit a := by
    rintro ⟨u, rfl⟩
    exact ha (mem_map_of_mem _ (mem_univ u))
  rw [MulChar.map_nonunit _ this, zero_mul]

/-- `ψ_k(q a) = ψ_d(a mod d)` when `k = d q`. -/
theorem s27_stdAddChar_mul {k d q : ℕ} [NeZero k] [NeZero d] (hkq : k = d * q) (hd : d ∣ k)
    (a : ZMod k) :
    ZMod.stdAddChar (N := k) ((q : ZMod k) * a) =
      ZMod.stdAddChar (N := d) (ZMod.castHom hd (ZMod d) a) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, (j : ZMod k) = a := ⟨a.val, by simp⟩
  have hq : (q : ZMod k) * (j : ZMod k) = ((q * j : ℤ) : ZMod k) := by
    push_cast; ring
  rw [hq, ZMod.stdAddChar_coe, map_intCast, ZMod.stdAddChar_coe]
  have hq0 : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := right_ne_zero_of_mul (hkq ▸ NeZero.ne k)
    exact_mod_cast this
  have hk : (k : ℂ) = d * q := by exact_mod_cast hkq
  congr 1
  rw [hk]
  push_cast
  field_simp

/-- Sums over the units through a surjective hom: `∑_u g(f u) = #ker · ∑_v g v`. -/
theorem s27_sum_comp_surjective {G H : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [DecidableEq H] (f : G →* H) (hf : Function.Surjective f) (g : H → ℂ) :
    ∑ u, g (f u) = (#{u | f u = 1} : ℂ) * ∑ v, g v := by
  classical
  rw [Finset.sum_comp, mul_sum]
  have him : (univ : Finset G).image f = univ := by
    ext v; simp only [mem_image, mem_univ, true_and, iff_true]; exact hf v
  rw [him]
  refine sum_congr rfl fun v _ ↦ ?_
  rw [nsmul_eq_mul]
  congr 2
  exact MonoidHom.card_fiber_eq_of_mem_range f (hf v) (hf 1)


/-- For `k = d q` with `d` the conductor, `G(q, χ) = #ker · G(1, χ*)`. -/
theorem s27_gaussSum_mulShift_conductor {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    [NeZero χ.conductor] {q : ℕ} (hkq : k = χ.conductor * q) :
    gaussSum χ ((ZMod.stdAddChar (N := k)).mulShift (q : ZMod k)) =
      (#{u | ZMod.unitsMap χ.conductor_dvd_level u = 1} : ℂ) *
        gaussSum χ.primitiveCharacter (ZMod.stdAddChar (N := χ.conductor)) := by
  classical
  set hd := χ.conductor_dvd_level
  rw [gaussSum, gaussSum, s27_sum_char_eq_sum_units, s27_sum_char_eq_sum_units]
  have hterm : ∀ u : (ZMod k)ˣ, χ u * ((ZMod.stdAddChar (N := k)).mulShift (q : ZMod k)) u =
      (fun v : (ZMod χ.conductor)ˣ ↦ χ.primitiveCharacter v *
        ZMod.stdAddChar (N := χ.conductor) v) (ZMod.unitsMap hd u) := by
    intro u
    simp only [AddChar.mulShift_apply]
    rw [s27_stdAddChar_mul hkq hd]
    congr 1
    · conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
      rw [DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
        MulChar.coe_toUnitHom]
  rw [sum_congr rfl fun u _ ↦ hterm u]
  convert s27_sum_comp_surjective _ (ZMod.unitsMap_surjective hd) _ using 1
  rfl


/-- §27.10 after 27.10.11 (proof). -/
theorem s27_isPrimitive_of_separable {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}
    (h : ∀ n, GaussSumSeparable χ n) : χ.IsPrimitive := by
  classical
  by_contra hnp
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨q, hkq⟩ := χ.conductor_dvd_level
  have hq1 : q ≠ 1 := by
    rintro rfl
    exact hnp (by rw [DirichletCharacter.isPrimitive_def]; omega)
  have hqk : q ∣ k := ⟨χ.conductor, by rw [mul_comm]; exact hkq⟩
  have hχq : χ q = 0 := by
    refine MulChar.map_nonunit _ ?_
    rw [ZMod.isUnit_iff_coprime, Nat.Coprime, Nat.gcd_eq_left hqk]
    exact hq1
  have h0 : gaussSumDLMF χ q = 0 := by
    rw [h q, hχq, _root_.map_zero, zero_mul]
  rw [gaussSumDLMF_eq_gaussSum, s27_gaussSum_mulShift_conductor χ hkq] at h0
  have hc : (#{u | ZMod.unitsMap χ.conductor_dvd_level u = 1} : ℂ) ≠ 0 := by
    have : 0 < #{u | ZMod.unitsMap χ.conductor_dvd_level u = 1} :=
      card_pos.mpr ⟨1, by simp⟩
    exact_mod_cast this.ne'
  have hG := r27_gaussSum_mul_conj χ.primitiveCharacter_isPrimitive
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact hc h1
  · rw [h1, zero_mul] at hG
    exact (NeZero.ne χ.conductor) (by exact_mod_cast hG.symm)

/-- §27.10 after 27.10.11: conversely, if `G(n, χ)` is separable for every `n`, then `χ` is
primitive. -/
@[dlmf 27.10]
theorem isPrimitive_of_separable {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}
    (h : ∀ n, GaussSumSeparable χ n) : χ.IsPrimitive :=
  s27_isPrimitive_of_separable h

/-- DLMF 27.10.12: a primitive character has the finite Fourier expansion
`χ(n) = (G(1, χ)/k) ∑_{m=1}^k χ̄(m) e^{-2πimn/k}`. -/
@[dlmf 27.10.E12]
theorem dirichletCharacter_fourier {k : ℕ} [NeZero k] {χ : DirichletCharacter ℂ k}
    (hχ : χ.IsPrimitive) (n : ℕ) :
    χ n = gaussSumDLMF χ 1 / k *
      ∑ m ∈ Finset.Icc 1 k, starRingEnd ℂ (χ m) * Complex.exp (-(2 * π * I * m * n / k)) := by
  have h1 : gaussSumDLMF χ 1 = gaussSum χ (ZMod.stdAddChar (N := k)) := by
    rw [gaussSumDLMF_eq_gaussSum, Nat.cast_one, AddChar.mulShift_one]
  have hsep : gaussSumDLMF χ n = starRingEnd ℂ (χ n) * gaussSumDLMF χ 1 := by
    rw [gaussSumDLMF_eq_gaussSum, r27_gaussSum_mulShift hχ, h1]
  have hs : ∑ m ∈ Finset.Icc 1 k, starRingEnd ℂ (χ m) * Complex.exp (-(2 * π * I * m * n / k)) =
      starRingEnd ℂ (gaussSumDLMF χ n) := by
    rw [gaussSumDLMF, map_sum]
    refine sum_congr rfl fun m _ ↦ ?_
    rw [map_mul, expFrac, ← Complex.exp_conj]
    congr 2
    simp [map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne k
  have hG := r27_gaussSum_mul_conj hχ
  rw [hs, hsep, map_mul, Complex.conj_conj, h1]
  field_simp
  linear_combination (-χ n) * hG

end DLMF.NumberTheory
