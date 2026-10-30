/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.JacobiElliptic.SpecialValues
public import DLMF.Lame.Eigenvalues
public import DLMF.Lame.Polynomials.P2pODE

/-!
# Lamé polynomials as Lamé eigenfunctions: eigenvalues (DLMF 29.15.7 and analogues)

On the real line the Lamé polynomial `lamePolyEk t n m` is real
(`p2p_E_ofReal`: `pre(x) P(sn² x)` with `P` of degree `n`), solves the real Lamé equation
(`p2p_re_sol`) and satisfies the boundary conditions of Table 29.3.2 of its type at `0` and
`K` (from the parities of Table 29.12.1). It has at most `n` zeros in `(0, K)`, since `sn²` is
injective there (`p2p_zeros_le`). By Sturm's oscillation theorem
(`ODE.p2s_oscillation_of_sol`) the number of zeros equals the number of eigenvalues below
`½(H_m + ν(ν+1)k²)`; these numbers increase strictly with `m` (29.15.3) and are at most `n`,
so they equal `m`: `½(H_m + ν(ν+1)k²)` is the `m`th eigenvalue (`p2p_lameEigenvalue_eq`).
-/

@[expose] public section

open Polynomial Complex DLMF.JacobiElliptic DLMF.Elliptic Filter Set
open scoped Topology Real

noncomputable section

namespace DLMF.Lame

/-- The boundary type at `0` of a Lamé polynomial type: odd (`w(0) = 0`) for a factor `sn`. -/
def p2p_odd0 : LamePolyType → Bool
  | .sE | .scE | .sdE | .scdE => true
  | _ => false

/-- The boundary type at `K`: odd (`w(K) = 0`) for a factor `cn`. -/
def p2p_oddK : LamePolyType → Bool
  | .cE | .scE | .cdE | .scdE => true
  | _ => false

/-- The real prefactor `cn^a dn^b sn^c` of a Lamé polynomial type on the real line. -/
def p2p_preR (t : LamePolyType) (x k : ℝ) : ℝ :=
  (match t with
    | .uE | .sE => 1
    | .cE | .scE => Real.jacobiCnm x (k ^ 2)
    | .dE | .sdE => Real.jacobiDnm x (k ^ 2)
    | .cdE | .scdE => Real.jacobiCnm x (k ^ 2) * Real.jacobiDnm x (k ^ 2)) *
  (match t with
    | .sE | .scE | .sdE | .scdE => Real.jacobiSnm x (k ^ 2)
    | _ => 1)

/-- On the real line a Lamé polynomial is real: `E(x) = pre(x) P(sn²x)`. -/
theorem p2p_E_ofReal {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) {n m : ℕ}
    (hm : m ≤ n) : ∃ P : ℝ[X], P ≠ 0 ∧ P.natDegree = n ∧ ∀ x : ℝ,
      lamePolyEk t n m x k =
        ((p2p_preR t x k * P.eval (Real.jacobiSnm x (k ^ 2) ^ 2) : ℝ) : ℂ) := by
  obtain ⟨P, hP, hE⟩ := p2p_polyForm hk0 hk1 t hm
  refine ⟨P, fun h0 => by simp [h0] at hP, natDegree_eq_of_degree_eq_some hP, fun x => ?_⟩
  rw [hE, jacobiSnk_ofReal hk0 hk1]
  have e : (P.map (algebraMap ℝ ℂ)).eval ((Real.jacobiSnm x (k ^ 2) : ℂ) ^ 2) =
      ((P.eval (Real.jacobiSnm x (k ^ 2) ^ 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Polynomial.eval_map]
    exact Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) _
  rw [e]
  cases t <;> simp [LamePolyType.prefactor, p2p_preR, jacobiCnk_ofReal hk0 hk1,
    jacobiDnk_ofReal hk0 hk1]

/-- On `(0, K)`: `0 < sn, cn` and `am ∈ (0, π/2)`. -/
lemma p2p_am_mem {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx : x ∈ Ioo 0 (Real.compEllIntKm (k ^ 2))) :
    Real.jacobiAmm x (k ^ 2) ∈ Ioo 0 (π / 2) := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hmono := p22R1_amm_strictMono hm
  constructor
  · have := hmono hx.1; simpa [Real.jacobiAmm_zero hm] using this
  · have := hmono hx.2; simpa [Real.jacobiAmm_compEllIntKm hm] using this

/-- For `0 < k < 1` and `0 < x < K`, `sn(x, k) > 0`. -/
theorem p2p_sn_pos {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx : x ∈ Ioo 0 (Real.compEllIntKm (k ^ 2))) : 0 < Real.jacobiSnm x (k ^ 2) := by
  have h := p2p_am_mem hk0 hk1 hx
  exact Real.sin_pos_of_pos_of_lt_pi h.1 (by linarith [h.2, Real.pi_pos])

/-- For `0 < k < 1` and `0 < x < K`, `cn(x, k) > 0`. -/
theorem p2p_cn_pos {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {x : ℝ}
    (hx : x ∈ Ioo 0 (Real.compEllIntKm (k ^ 2))) : 0 < Real.jacobiCnm x (k ^ 2) := by
  have h := p2p_am_mem hk0 hk1 hx
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1, Real.pi_pos], h.2⟩

/-- `sn²` is injective on `(0, K)`. -/
theorem p2p_sn_sq_injOn {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) :
    InjOn (fun x => Real.jacobiSnm x (k ^ 2) ^ 2) (Ioo 0 (Real.compEllIntKm (k ^ 2))) := by
  intro x hx y hy hxy
  have hm : k ^ 2 < 1 := by nlinarith
  have h1 : Real.jacobiSnm x (k ^ 2) = Real.jacobiSnm y (k ^ 2) := by
    have := p2p_sn_pos hk0 hk1 hx
    have := p2p_sn_pos hk0 hk1 hy
    simp only at hxy
    nlinarith [sq_nonneg (Real.jacobiSnm x (k ^ 2) - Real.jacobiSnm y (k ^ 2))]
  have ax := p2p_am_mem hk0 hk1 hx
  have ay := p2p_am_mem hk0 hk1 hy
  have h2 : Real.jacobiAmm x (k ^ 2) = Real.jacobiAmm y (k ^ 2) :=
    Real.injOn_sin ⟨by linarith [ax.1, Real.pi_pos], by linarith [ax.2]⟩
      ⟨by linarith [ay.1, Real.pi_pos], by linarith [ay.2]⟩ h1
  exact (p22R1_amm_strictMono hm).injective h2

/-- The prefactor is nonzero on `(0, K)`. -/
lemma p2p_preR_ne {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) {x : ℝ}
    (hx : x ∈ Ioo 0 (Real.compEllIntKm (k ^ 2))) : p2p_preR t x k ≠ 0 := by
  have hm : k ^ 2 < 1 := by nlinarith
  have hs := (p2p_sn_pos hk0 hk1 hx).ne'
  have hc := (p2p_cn_pos hk0 hk1 hx).ne'
  have hd := (Real.jacobiDnm_pos hm x).ne'
  cases t <;> simp [p2p_preR, hs, hc, hd]

/-- The zeros of a Lamé polynomial in `(0, K)`: finitely many, at most `n`, and not all of
`(0, K)`. -/
theorem p2p_zeros_le {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType) {n m : ℕ}
    (hm : m ≤ n) :
    {x | x ∈ Ioo 0 (Real.compEllIntKm (k ^ 2)) ∧ (lamePolyEk t n m x k).re = 0}.Finite ∧
    {x | x ∈ Ioo 0 (Real.compEllIntKm (k ^ 2)) ∧ (lamePolyEk t n m x k).re = 0}.ncard ≤ n ∧
    (fun x : ℝ => (lamePolyEk t n m x k).re) ≠ 0 := by
  obtain ⟨P, hP0, hPd, hE⟩ := p2p_E_ofReal hk0 hk1 t hm
  set Z := {x | x ∈ Ioo 0 (Real.compEllIntKm (k ^ 2)) ∧ (lamePolyEk t n m x k).re = 0}
  have hmaps : ∀ x ∈ Z, (fun x => Real.jacobiSnm x (k ^ 2) ^ 2) x ∈ (P.roots.toFinset : Set ℝ) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [hE, Complex.ofReal_re] at hx2
    have := (mul_eq_zero.mp hx2).resolve_left (p2p_preR_ne hk0 hk1 t hx1)
    simp [Multiset.mem_toFinset, mem_roots hP0, this]
  have hinj : InjOn (fun x => Real.jacobiSnm x (k ^ 2) ^ 2) Z :=
    (p2p_sn_sq_injOn hk0 hk1).mono fun x hx => hx.1
  have hfin : Z.Finite := Set.Finite.of_injOn hmaps hinj (Finset.finite_toSet _)
  refine ⟨hfin, ?_, fun h0 => ?_⟩
  · calc Z.ncard ≤ (P.roots.toFinset : Set ℝ).ncard :=
          Set.ncard_le_ncard_of_injOn _ hmaps hinj (Finset.finite_toSet _)
      _ = P.roots.toFinset.card := Set.ncard_coe_finset _
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := card_roots' P
      _ = n := hPd
  · have hK : 0 < Real.compEllIntKm (k ^ 2) := Real.compEllIntKm_pos (by nlinarith)
    have : Ioo 0 (Real.compEllIntKm (k ^ 2)) ⊆ Z := fun x hx =>
      ⟨hx, by simpa using congrFun h0 x⟩
    exact (Set.Ioo_infinite hK) (hfin.subset this)

/-- A function with reflection symmetry `E(p - z) = σ E(p + z)` vanishes at `p` (`σ = -1`) or
has vanishing derivative there (`σ = 1`). -/
theorem p2p_sym_vals {E : ℂ → ℂ} {p σ : ℂ} (hd : DifferentiableAt ℂ E p)
    (hE : ∀ z, E (p - z) = σ * E (p + z)) : (σ = -1 → E p = 0) ∧ (σ = 1 → deriv E p = 0) := by
  refine ⟨fun hσ => ?_, fun hσ => ?_⟩
  · have := hE 0
    simp only [sub_zero, add_zero, hσ] at this
    linear_combination this / 2
  · have a1 : HasDerivAt (fun z => E (p + z)) (deriv E p) 0 :=
      HasDerivAt.comp_const_add p 0 (by simpa using hd.hasDerivAt)
    have a2 : HasDerivAt (fun z => E (p - z)) (-deriv E p) 0 :=
      HasDerivAt.comp_const_sub p 0 (by simpa using hd.hasDerivAt)
    have e : (fun z => E (p - z)) = fun z => E (p + z) := funext fun z => by simp [hE z, hσ]
    rw [e] at a2
    have := a1.unique a2
    linear_combination this / 2

/-- The real part along `ℝ` of a complex solution of Lamé's equation with real parameters, regular
on `ℝ`, is a real solution. -/
lemma p2p_re_sol {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) {h ν : ℝ} {E : ℂ → ℂ}
    (hE : IsLameSolutionOn (h : ℂ) (ν : ℂ) (k : ℂ) E {z | JacobiRegulark .n z k}) :
    Real.IsLameSolution h ν k (fun x : ℝ => (E x).re) ∧
      ∀ x : ℝ, deriv (fun x : ℝ => (E x).re) x = (deriv E x).re := by
  have r : ∀ x : ℝ, JacobiRegulark .n (x : ℂ) k := p2p_regular_real hk0 hk1
  have d1 : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (E x).re) (deriv E x).re x := fun x =>
    (hE.differentiableAt _ (r x)).hasDerivAt.real_of_complex
  have hd : deriv (fun x : ℝ => (E x).re) = fun x : ℝ => (deriv E x).re :=
    funext fun x => (d1 x).deriv
  refine ⟨⟨fun x => (d1 x).differentiableAt, fun x => ?_⟩, fun x => (d1 x).deriv⟩
  rw [hd]
  have := (hE.hasDerivAt_deriv _ (r x)).real_of_complex
  convert this using 1
  rw [jacobiSnk_ofReal hk0 hk1]
  have e : (-((h : ℂ) - ν * (ν + 1) * (k : ℂ) ^ 2 * (Real.jacobiSnm x (k ^ 2) : ℂ) ^ 2) : ℂ) =
      ((-(h - ν * (ν + 1) * k ^ 2 * Real.jacobiSnm x (k ^ 2) ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]

/-- On the real line the Lamé polynomial `lamePolyEk t n j` is an eigenfunction of the Lamé
problem of Table 29.3.2 with the boundary types of `t`, for `½(H_j + ν(ν+1)k²)`. -/
theorem p2p_isLameEigenfunction {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n j : ℕ} (hj : j ≤ n) :
    Real.IsLameEigenfunction ((lamePolyH t n j k + (t.order n : ℝ) * ((t.order n : ℝ) + 1) *
      k ^ 2) / 2) (t.order n : ℝ) k (p2p_odd0 t) (p2p_oddK t)
      (fun x : ℝ => (lamePolyEk t n j x k).re) := by
  set ν : ℝ := (t.order n : ℝ) with hνdef
  set hv : ℕ → ℝ := fun j => (lamePolyH t n j k + ν * (ν + 1) * k ^ 2) / 2 with hhv
  have hsol := p2p_lamePolyEk_isLameSolution hk0 hk1 t hj
  have hcast : ((lamePolyH t n j k + t.order n * (t.order n + 1) * k ^ 2) / 2 : ℂ) =
      ((hv j : ℝ) : ℂ) := by simp only [hhv, ν]; push_cast; ring
  rw [hcast, show ((t.order n : ℕ) : ℂ) = ((ν : ℝ) : ℂ) by simp [ν]] at hsol
  obtain ⟨hre, hder⟩ := p2p_re_sol hk0 hk1 hsol
  set w := fun x : ℝ => (lamePolyEk t n j x k).re
  obtain ⟨-, -, hne⟩ := p2p_zeros_le hk0 hk1 t hj
  obtain ⟨s1, s2, -⟩ := p2p_lamePolyEk_sym hk0 hk1 t n j
  have v0 := p2p_sym_vals (E := fun z => lamePolyEk t n j z k) (p := 0)
    (hsol.differentiableAt _ (by simpa using p2p_regular_real hk0 hk1 0)) s1
  have vK := p2p_sym_vals (E := fun z => lamePolyEk t n j z k)
    (hsol.differentiableAt _ (p2p_regular_real hk0 hk1 _)) s2
  have e0 : p2p_sgnS t = if p2p_odd0 t then -1 else 1 := by cases t <;> rfl
  have eK : p2p_sgnC t = if p2p_oddK t then -1 else 1 := by cases t <;> rfl
  have hbc : Real.LameBoundary k (p2p_odd0 t) (p2p_oddK t) w := by
    refine ⟨?_, ?_⟩
    · by_cases ho : p2p_odd0 t = true
      · simp only [ho, ite_true] at e0 ⊢
        have := v0.1 e0
        simp only [w]; simpa using congrArg Complex.re this
      · simp only [ho, Bool.false_eq_true, ite_false] at e0 ⊢
        have := v0.2 e0
        rw [hder]; simpa using congrArg Complex.re this
    · by_cases ho : p2p_oddK t = true
      · simp only [ho, ite_true] at eK ⊢
        have := vK.1 eK
        simp only [w]; simpa using congrArg Complex.re this
      · simp only [ho, Bool.false_eq_true, ite_false] at eK ⊢
        have := vK.2 eK
        rw [hder]; simpa using congrArg Complex.re this
  exact ⟨hre, hbc, hne⟩

/-- The Lamé polynomials are the eigenfunctions of the first `n + 1` eigenvalues: the
eigenvalue `½(H_m + ν(ν+1)k²)` (`ν = t.order n`, `m ≤ n`) is the `m`th eigenvalue of the
problem of Table 29.3.2 with the boundary types of `t`. Proved by Sturm's oscillation theorem:
the `n + 1` eigenfunctions have at most `n` zeros in `(0, K)` and increasing eigenvalues. -/
theorem p2p_lameEigenvalue_eq {k : ℝ} (hk0 : 0 < k) (hk1 : k < 1) (t : LamePolyType)
    {n m : ℕ} (hm : m ≤ n) :
    Real.lameEigenvalue (t.order n : ℝ) k (p2p_odd0 t) (p2p_oddK t) m =
      (lamePolyH t n m k + (t.order n : ℝ) * ((t.order n : ℝ) + 1) * k ^ 2) / 2 := by
  have hk : k ^ 2 < 1 := by nlinarith
  have hK : 0 < Real.compEllIntKm (k ^ 2) := Real.compEllIntKm_pos hk
  set ν : ℝ := (t.order n : ℝ) with hνdef
  set hv : ℕ → ℝ := fun j => (lamePolyH t n j k + ν * (ν + 1) * k ^ 2) / 2 with hhv
  set S := Real.lameSpectrum ν k (p2p_odd0 t) (p2p_oddK t)
  have hS := p2l_lameSpectrum_eq (ν := ν) (k := k) (p2p_odd0 t) (p2p_oddK t)
  have hfin : ∀ c, (S ∩ Iio c).Finite := fun c => by
    simp only [S, hS]
    exact ODE.p2l_spec_Iio_finite (p2lPot_continuous hk) p2lPot_abs_le hK _ _ c
  -- each `j ≤ n` gives an eigenfunction with at most `n` zeros
  have key : ∀ j ≤ n, hv j ∈ S ∧ (S ∩ Iio (hv j)).ncard ≤ n := by
    intro j hj
    obtain ⟨hre, hbc, hne⟩ : Real.IsLameEigenfunction (hv j) ν k (p2p_odd0 t) (p2p_oddK t)
        (fun x : ℝ => (lamePolyEk t n j x k).re) := p2p_isLameEigenfunction hk0 hk1 t hj
    set w := fun x : ℝ => (lamePolyEk t n j x k).re
    obtain ⟨hZf, hZn, -⟩ := p2p_zeros_le hk0 hk1 t hj
    have hmem : hv j ∈ S := ⟨w, hre, hbc, hne⟩
    refine ⟨hmem, ?_⟩
    have hosc := ODE.p2s_oscillation_of_sol (p2lPot_continuous hk) p2lPot_abs_le hK
      (p2p_odd0 t) (p2p_oddK t) ((p2l_isLameSolution_iff).mp hre) hbc hne
    rw [← hS] at hosc
    have : (S ∩ Iio (hv j)).ncard =
        {x | x ∈ Ioo 0 (Real.compEllIntKm (k ^ 2)) ∧ w x = 0}.ncard := by
      rw [← Set.Finite.cast_ncard_eq (hfin _), ← Set.Finite.cast_ncard_eq hZf] at hosc
      exact_mod_cast hosc.symm
    rw [this]; exact hZn
  -- counting
  set f : ℕ → ℕ := fun j => (S ∩ Iio (hv j)).ncard
  have hmono : ∀ i j, i < j → j ≤ n → f i < f j := by
    intro i j hij hj
    have hlt : hv i < hv j := by
      simp only [hhv]
      linarith [p2p_lamePolyH_lt hk0 hk1 t hij hj]
    refine Set.ncard_lt_ncard ?_ (hfin _)
    refine ⟨fun x hx => ⟨hx.1, lt_trans hx.2 hlt⟩, fun hsub => ?_⟩
    exact lt_irrefl _ (Set.mem_Iio.mp (hsub ⟨(key i (by omega)).1, hlt⟩).2)
  have hlow : ∀ j ≤ n, j ≤ f j := by
    intro j
    induction j with
    | zero => intro _; omega
    | succ j ih => intro hj; have := hmono j (j + 1) (by omega) hj; have := ih (by omega); omega
  have hup : ∀ d ≤ n, f (n - d) ≤ n - d := by
    intro d
    induction d with
    | zero => intro _; simpa using (key n le_rfl).2
    | succ d ih =>
      intro hd
      have := hmono (n - (d + 1)) (n - d) (by omega) (by omega)
      have := ih (by omega)
      omega
  have hfm : f m = m := by
    have := hup (n - m) (by omega)
    rw [show n - (n - m) = m by omega] at this
    have := hlow m hm
    omega
  -- identification
  have hnth : Real.IsNthLameEigenvalue ν k (p2p_odd0 t) (p2p_oddK t) m (hv m) :=
    ⟨(key m hm).1, hfin _, hfm⟩
  have hν : -1 / 2 ≤ ν := by simp only [ν]; have := Nat.cast_nonneg (α := ℝ) (t.order n); linarith
  have huniq := (Real.lameEigenvalue_spec hν hk0 hk1 (p2p_odd0 t) (p2p_oddK t)).1 m
  exact huniq.unique (Real.isNthLameEigenvalue_lameEigenvalue hν hk0 hk1 _ _ m) hnth

end DLMF.Lame
