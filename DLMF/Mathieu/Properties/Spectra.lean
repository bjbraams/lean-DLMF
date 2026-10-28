/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Properties.Floquet

/-!
# Mathieu characteristic spectra

Eigenvalue characterizations, spectral discreteness and the zero-parameter Mathieu spectrum.

Source references and common attribution are retained in
`DLMF.Mathieu.Properties`.
-/

@[expose] public noncomputable section

open Complex Set Filter ComplexConjugate

open scoped Topology Real

namespace DLMF.Mathieu

/-! ### Eigenvalues (§28.2(v)) -/

/-- **Discrete set of eigenvalues** (DLMF §28.2(v)): for given `ν` and `q`, the set of `a`
satisfying the characteristic equation 28.2.16 is infinite and has no finite accumulation
point. -/
@[dlmf 28.2.v]
theorem charExp_set_infinite_discrete (q ν : ℂ) :
    {a : ℂ | IsMathieuCharExp a q ν}.Infinite ∧
      ∀ K : Set ℂ, IsCompact K → (K ∩ {a : ℂ | IsMathieuCharExp a q ν}).Finite := by
  sorry

/-- **DLMF 28.2.21** (even `n`): `w_I'(π/2; a_{2n}(q), q) = 0`. -/
@[dlmf 28.2.E21]
theorem deriv_mathieuWI_half_pi_mathieuA_even (n : ℕ) (q : ℝ) :
    deriv (mathieuWI (mathieuA (2 * n) q) q) (π / 2) = 0 := by
  have := (mathieuA_spec (2 * n) q).1
  simpa [mathieuSpecA] using this

/-- **DLMF 28.2.21** (odd `n`): `w_I(π/2; a_{2n+1}(q), q) = 0`. -/
@[dlmf 28.2.E21]
theorem mathieuWI_half_pi_mathieuA_odd (n : ℕ) (q : ℝ) :
    mathieuWI (mathieuA (2 * n + 1) q) q (π / 2) = 0 := by
  have := (mathieuA_spec (2 * n + 1) q).1
  simpa [mathieuSpecA, Nat.not_even_bit1] using this

/-- **DLMF 28.2.22** (odd `n`): `w_II'(π/2; b_{2n+1}(q), q) = 0`. -/
@[dlmf 28.2.E22]
theorem deriv_mathieuWII_half_pi_mathieuB_odd (n : ℕ) (q : ℝ) :
    deriv (mathieuWII (mathieuB (2 * n + 1) q) q) (π / 2) = 0 := by
  have := (mathieuB_spec (n := 2 * n + 1) (by omega) q).1
  simpa [mathieuSpecB, Nat.not_even_bit1] using this

/-- **DLMF 28.2.22** (even `n`): `w_II(π/2; b_{2n+2}(q), q) = 0`. -/
@[dlmf 28.2.E22]
theorem mathieuWII_half_pi_mathieuB_even (n : ℕ) (q : ℝ) :
    mathieuWII (mathieuB (2 * n + 2) q) q (π / 2) = 0 := by
  have := (mathieuB_spec (n := 2 * n + 2) (by omega) q).1
  have he : Even (2 * n + 2) := ⟨n + 1, by ring⟩
  simpa [mathieuSpecB, he] using this

/-! ### Discreteness of the spectra -/

/-- An entire function that does not vanish at some real point has finitely many real zeros in
every compact interval. -/
lemma p1a1_finite_real_zeros {g : ℂ → ℂ} (hg : Differentiable ℂ g) {y : ℝ} (hy : g y ≠ 0)
    (s t : ℝ) : {x : ℝ | x ∈ Icc s t ∧ g x = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf isCompact_Icc
    (fun x hx => hx.1)
  rw [accPt_iff_frequently_nhdsNE] at hx
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (Complex.continuous_ofReal.tendsto x).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact fun h => hz (Complex.ofReal_injective h)
  have hfr : ∃ᶠ z in 𝓝[≠] (x : ℂ), g z = 0 :=
    ht.frequently (hx.mono fun z hz => hz.2)
  have := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (fun z _ => hg.analyticAt z) isPreconnected_univ (mem_univ (x : ℂ)) hfr (mem_univ (y : ℂ))
  exact hy this

/-- A set of zeros of such a function, bounded below, has finitely many elements below any `a`. -/
lemma p1a1_spec_finite {S : Set ℝ} {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hSg : ∀ x ∈ S, g x = 0) {x₀ : ℝ} (hx₀ : ∀ y ∈ S, x₀ ≤ y) {y : ℝ} (hy : g y ≠ 0) (a : ℝ) :
    (S ∩ Iio a).Finite :=
  (p1a1_finite_real_zeros hg hy x₀ a).subset fun x hx =>
    ⟨⟨hx₀ x hx.1, (Set.mem_Iio.mp hx.2).le⟩, hSg x hx.1⟩

/-- An element of `S` with finitely many smaller elements is some `nthLeast S k`. -/
theorem p1a1_exists_eq_nthLeast {S : Set ℝ} {a : ℝ} (ha : a ∈ S) (hfin : (S ∩ Iio a).Finite) :
    ∃ k : ℕ, a = nthLeast S k :=
  ⟨(S ∩ Iio a).ncard, (nthLeast_eq_of ha hfin.cast_ncard_eq.symm).symm⟩

/-- The least element of a spectrum. -/
lemma p1a1_le_of_encard_zero {S : Set ℝ} {x₀ : ℝ} (h : (S ∩ Iio x₀).encard = (0 : ℕ)) :
    ∀ y ∈ S, x₀ ≤ y := by
  intro y hy
  by_contra hlt
  rw [not_le] at hlt
  have : (S ∩ Iio x₀) = ∅ := by exact_mod_cast Set.encard_eq_zero.mp (by exact_mod_cast h)
  exact (Set.eq_empty_iff_forall_notMem.mp this) y ⟨hy, hlt⟩

/-- `a ↦ w_I(z; a, q)` and `a ↦ w_II(z; a, q)` are entire (from 28.2(ii)). -/
lemma p1a1_differentiable_param (z q : ℂ) :
    Differentiable ℂ (fun a => mathieuWI a q z) ∧ Differentiable ℂ (fun a => mathieuWII a q z) := by
  have hl : Differentiable ℂ (fun a : ℂ => (z, a, q)) := by fun_prop
  exact ⟨differentiable_mathieuWI_mathieuWII.1.comp hl,
    differentiable_mathieuWI_mathieuWII.2.comp hl⟩

/-- A spectrum with an element having no smaller elements is bounded below. -/
lemma p1a1_least (S : Set ℝ) (h : ∃ x ∈ S, (S ∩ Iio x).encard = (0 : ℕ)) :
    ∃ x₀, ∀ y ∈ S, x₀ ≤ y := by
  obtain ⟨x, -, hx⟩ := h; exact ⟨x, p1a1_le_of_encard_zero hx⟩

/-- **Table 28.2.1** (`ν̂ = 0`, `w'(0) = w'(π/2) = 0`): for real `q` the even `π`-periodic
solutions occur exactly for `a = a_{2n}(q)`: a nontrivial solution with `w'(0) = w'(π/2) = 0`
exists iff `a = a_{2n}(q)` for some `n`. -/
@[dlmf 28.2.T1]
theorem exists_solution_neumann_iff (a q : ℝ) :
    (∃ w, IsMathieuSolution a q w ∧ w ≠ 0 ∧ deriv w 0 = 0 ∧ deriv w (π / 2) = 0) ↔
      ∃ n : ℕ, a = mathieuA (2 * n) q := by
  constructor
  · rintro ⟨w, hw, hne, h0, h1⟩
    have hw0 : w 0 ≠ 0 := by
      intro h; apply hne; rw [hw.eq_combination]; funext z; simp [h, h0]
    have hA' : deriv (mathieuWI a q) (π / 2) = 0 := by
      have := hw.p1a1_deriv_eq (π / 2)
      rw [h0, zero_mul, add_zero, h1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hw0
    set S := mathieuSpecA 0 q
    have hS : ∀ k, mathieuSpecA (2 * k) q = S := by
      intro k; simp [S, mathieuSpecA]
    have haS : a ∈ S := by simpa [S, mathieuSpecA] using hA'
    obtain ⟨x₀, hx₀⟩ := p1a1_least S (mathieuSpecA_exists 0 q 0)
    obtain ⟨y₀, hy₀⟩ := p1a1_least (mathieuSpecB 2 q) (mathieuSpecB_exists 2 q 0)
    have hfin : (S ∩ Iio a).Finite := by
      refine p1a1_spec_finite (g := fun b => mathieuWI b q π - 1)
        ((p1a1_differentiable_param _ _).1.sub_const 1) (fun x hx => ?_) hx₀
        (y := min x₀ y₀ - 1) ?_ a
      · have : deriv (mathieuWI x q) (π / 2) = 0 := by simpa [S, mathieuSpecA] using hx
        simp only [mathieuWI_pi_sub_one, this]; ring
      · intro h0
        simp only [mathieuWI_pi_sub_one] at h0
        rcases mul_eq_zero.mp h0 with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · have := hx₀ (min x₀ y₀ - 1) (by
              simp only [S, mathieuSpecA, Even.zero, ↓reduceIte, Set.mem_ofPred_eq]; exact h)
            linarith [min_le_left x₀ y₀]
        · have := hy₀ (min x₀ y₀ - 1) (by
            simp only [mathieuSpecB, even_two, ↓reduceIte, Set.mem_ofPred_eq]; exact h)
          linarith [min_le_right x₀ y₀]
    obtain ⟨k, hk⟩ := p1a1_exists_eq_nthLeast haS hfin
    refine ⟨k, ?_⟩
    rw [hk, mathieuA, hS, show 2 * k / 2 = k by omega]
  · rintro ⟨n, rfl⟩
    obtain ⟨h1, h10, h11⟩ := mathieuWI_spec (mathieuA (2 * n) q : ℂ) q
    exact ⟨_, h1, fun h => by simpa [h10] using congrFun h 0, h11,
      deriv_mathieuWI_half_pi_mathieuA_even n q⟩

/-- **Table 28.2.1** (`ν̂ = 1`, `w'(0) = w(π/2) = 0`): exactly for `a = a_{2n+1}(q)`. -/
@[dlmf 28.2.T1]
theorem exists_solution_neumann_dirichlet_iff (a q : ℝ) :
    (∃ w, IsMathieuSolution a q w ∧ w ≠ 0 ∧ deriv w 0 = 0 ∧ w (π / 2) = 0) ↔
      ∃ n : ℕ, a = mathieuA (2 * n + 1) q := by
  constructor
  · rintro ⟨w, hw, hne, h0, h1⟩
    have hw0 : w 0 ≠ 0 := by
      intro h; apply hne; rw [hw.eq_combination]; funext z; simp [h, h0]
    have hA : mathieuWI a q (π / 2) = 0 := by
      have := congrFun hw.eq_combination (π / 2)
      rw [h0, zero_mul, add_zero, h1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hw0
    set S := mathieuSpecA 1 q
    have hS : ∀ k, mathieuSpecA (2 * k + 1) q = S := by
      intro k; simp [S, mathieuSpecA, Nat.not_even_bit1]
    have hmem : ∀ x : ℝ, x ∈ S ↔ mathieuWI x q (π / 2) = 0 := by
      intro x; simp only [S, mathieuSpecA, Nat.not_even_one, ↓reduceIte, Set.mem_ofPred_eq]
    obtain ⟨x₀, hx₀⟩ := p1a1_least S (mathieuSpecA_exists 1 q 0)
    have hfin : (S ∩ Iio a).Finite := by
      refine p1a1_spec_finite (g := fun b => mathieuWI b q (π / 2))
        (p1a1_differentiable_param _ _).1 (fun x hx => (hmem x).mp hx) hx₀
        (y := x₀ - 1) (fun h0 => ?_) a
      have := hx₀ _ ((hmem _).mpr h0); linarith
    obtain ⟨k, hk⟩ := p1a1_exists_eq_nthLeast ((hmem a).mpr hA) hfin
    refine ⟨k, ?_⟩
    rw [hk, mathieuA, hS, show (2 * k + 1) / 2 = k by omega]
  · rintro ⟨n, rfl⟩
    obtain ⟨h1, h10, h11⟩ := mathieuWI_spec (mathieuA (2 * n + 1) q : ℂ) q
    exact ⟨_, h1, fun h => by simpa [h10] using congrFun h 0, h11,
      mathieuWI_half_pi_mathieuA_odd n q⟩

/-- **Table 28.2.1** (`ν̂ = 1`, `w(0) = w'(π/2) = 0`): exactly for `a = b_{2n+1}(q)`. -/
@[dlmf 28.2.T1]
theorem exists_solution_dirichlet_neumann_iff (a q : ℝ) :
    (∃ w, IsMathieuSolution a q w ∧ w ≠ 0 ∧ w 0 = 0 ∧ deriv w (π / 2) = 0) ↔
      ∃ n : ℕ, a = mathieuB (2 * n + 1) q := by
  constructor
  · rintro ⟨w, hw, hne, h0, h1⟩
    have hw0 : deriv w 0 ≠ 0 := by
      intro h; apply hne; rw [hw.eq_combination]; funext z; simp [h, h0]
    have hB' : deriv (mathieuWII a q) (π / 2) = 0 := by
      have := hw.p1a1_deriv_eq (π / 2)
      rw [h0, zero_mul, zero_add, h1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hw0
    set S := mathieuSpecB 1 q
    have hS : ∀ k, mathieuSpecB (2 * k + 1) q = S := by
      intro k; simp [S, mathieuSpecB, Nat.not_even_bit1]
    have hmem : ∀ x : ℝ, x ∈ S ↔ deriv (mathieuWII x q) (π / 2) = 0 := by
      intro x; simp only [S, mathieuSpecB, Nat.not_even_one, ↓reduceIte, Set.mem_ofPred_eq]
    have hmemA : ∀ x : ℝ, x ∈ mathieuSpecA 1 q ↔ mathieuWI x q (π / 2) = 0 := by
      intro x; simp only [mathieuSpecA, Nat.not_even_one, ↓reduceIte, Set.mem_ofPred_eq]
    obtain ⟨x₀, hx₀⟩ := p1a1_least S (mathieuSpecB_exists 1 q 0)
    obtain ⟨y₀, hy₀⟩ := p1a1_least (mathieuSpecA 1 q) (mathieuSpecA_exists 1 q 0)
    have hfin : (S ∩ Iio a).Finite := by
      refine p1a1_spec_finite (g := fun b => mathieuWI b q π + 1)
        ((p1a1_differentiable_param _ _).1.add_const 1) (fun x hx => ?_) hx₀
        (y := min x₀ y₀ - 1) ?_ a
      · simp only [mathieuWI_pi_add_one, (hmem x).mp hx]; ring
      · intro h0
        simp only [mathieuWI_pi_add_one] at h0
        rcases mul_eq_zero.mp h0 with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · have := hy₀ _ ((hmemA _).mpr h)
            linarith [min_le_right x₀ y₀]
        · have := hx₀ _ ((hmem _).mpr h)
          linarith [min_le_left x₀ y₀]
    obtain ⟨k, hk⟩ := p1a1_exists_eq_nthLeast ((hmem a).mpr hB') hfin
    refine ⟨k, ?_⟩
    rw [hk]; simp only [mathieuB, show 2 * k + 1 ≠ 0 by omega, ↓reduceIte]
    rw [hS, show (2 * k + 1 - 1) / 2 = k by omega]
  · rintro ⟨n, rfl⟩
    obtain ⟨h1, h10, h11⟩ := mathieuWII_spec (mathieuB (2 * n + 1) q : ℂ) q
    exact ⟨_, h1, fun h => by
      have := congrArg (fun f => deriv f 0) h; simp [h11] at this, h10,
      deriv_mathieuWII_half_pi_mathieuB_odd n q⟩

/-- **Table 28.2.1** (`ν̂ = 0`, `w(0) = w(π/2) = 0`): exactly for `a = b_{2n+2}(q)`. -/
@[dlmf 28.2.T1]
theorem exists_solution_dirichlet_iff (a q : ℝ) :
    (∃ w, IsMathieuSolution a q w ∧ w ≠ 0 ∧ w 0 = 0 ∧ w (π / 2) = 0) ↔
      ∃ n : ℕ, a = mathieuB (2 * n + 2) q := by
  constructor
  · rintro ⟨w, hw, hne, h0, h1⟩
    have hw0 : deriv w 0 ≠ 0 := by
      intro h; apply hne; rw [hw.eq_combination]; funext z; simp [h, h0]
    have hB : mathieuWII a q (π / 2) = 0 := by
      have := congrFun hw.eq_combination (π / 2)
      rw [h0, zero_mul, zero_add, h1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hw0
    set S := mathieuSpecB 2 q
    have hS : ∀ k, mathieuSpecB (2 * k + 2) q = S := by
      intro k
      have : Even (2 * k + 2) := ⟨k + 1, by ring⟩
      simp [S, mathieuSpecB, this]
    have hmem : ∀ x : ℝ, x ∈ S ↔ mathieuWII x q (π / 2) = 0 := by
      intro x; simp only [S, mathieuSpecB, even_two, ↓reduceIte, Set.mem_ofPred_eq]
    obtain ⟨x₀, hx₀⟩ := p1a1_least S (mathieuSpecB_exists 2 q 0)
    have hfin : (S ∩ Iio a).Finite := by
      refine p1a1_spec_finite (g := fun b => mathieuWII b q (π / 2))
        (p1a1_differentiable_param _ _).2 (fun x hx => (hmem x).mp hx) hx₀
        (y := x₀ - 1) (fun h0 => ?_) a
      have := hx₀ _ ((hmem _).mpr h0); linarith
    obtain ⟨k, hk⟩ := p1a1_exists_eq_nthLeast ((hmem a).mpr hB) hfin
    refine ⟨k, ?_⟩
    rw [hk]; simp only [mathieuB, show 2 * k + 2 ≠ 0 by omega, ↓reduceIte]
    rw [hS, show (2 * k + 2 - 1) / 2 = k by omega]
  · rintro ⟨n, rfl⟩
    obtain ⟨h1, h10, h11⟩ := mathieuWII_spec (mathieuB (2 * n + 2) q : ℂ) q
    exact ⟨_, h1, fun h => by
      have := congrArg (fun f => deriv f 0) h; simp [h11] at this, h10,
      mathieuWII_half_pi_mathieuB_even n q⟩

/-- The `(k+1)`-st smallest element exceeds the `k`-th. -/
lemma p1a1_nthLeast_lt {S : Set ℝ} {k : ℕ} (hk : ∃ x ∈ S, (S ∩ Iio x).encard = k)
    (hk1 : ∃ x ∈ S, (S ∩ Iio x).encard = (k + 1 : ℕ)) : nthLeast S k < nthLeast S (k + 1) := by
  obtain ⟨-, hx⟩ := nthLeast_spec hk
  obtain ⟨-, hy⟩ := nthLeast_spec hk1
  by_contra hle
  rw [not_lt] at hle
  have h := Set.encard_le_encard (inter_subset_inter_right S (Iio_subset_Iio hle))
  rw [hx, hy] at h
  have : ((k + 1 : ℕ) : ℕ∞) ≤ k := h
  norm_cast at this
  omega

/-- **Monotone ordering** within each spectrum (DLMF §28.2(v)): `a_{2n} < a_{2n+2}`,
`a_{2n+1} < a_{2n+3}`, `b_{2n+1} < b_{2n+3}`, `b_{2n+2} < b_{2n+4}` (real `q`). -/
@[dlmf 28.2.v]
theorem mathieuA_lt_mathieuA_add_two (n : ℕ) (q : ℝ) : mathieuA n q < mathieuA (n + 2) q := by
  have hS : mathieuSpecA (n + 2) q = mathieuSpecA n q := by
    simp [mathieuSpecA, Nat.even_add]
  simp only [mathieuA, hS, show (n + 2) / 2 = n / 2 + 1 by omega]
  exact p1a1_nthLeast_lt (mathieuSpecA_exists n q _) (mathieuSpecA_exists n q _)

/-- Monotone ordering within each spectrum of the `b_n` (DLMF §28.2(v)), `n ≥ 1`. -/
@[dlmf 28.2.v]
theorem mathieuB_lt_mathieuB_add_two {n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    mathieuB n q < mathieuB (n + 2) q := by
  have hS : mathieuSpecB (n + 2) q = mathieuSpecB n q := by
    simp [mathieuSpecB, Nat.even_add]
  simp only [mathieuB, hn, show n + 2 ≠ 0 by omega, ite_false, hS,
    show (n + 2 - 1) / 2 = (n - 1) / 2 + 1 by omega]
  exact p1a1_nthLeast_lt (mathieuSpecB_exists n q _) (mathieuSpecB_exists n q _)

/-- The eigenvalues `a_n(q)` are pairwise distinct. -/
lemma p1a1_mathieuA_injective (q : ℝ) : Function.Injective fun n => mathieuA n q := by
  intro m n hmn
  simp only at hmn
  have hW := mathieuWI_wronskian (mathieuA m q) q (π / 2)
  obtain ⟨hm1, hm2⟩ := mathieuA_spec m q
  obtain ⟨hn1, hn2⟩ := mathieuA_spec n q
  rcases Nat.even_or_odd m with hm | hm <;> rcases Nat.even_or_odd n with hn | hn
  · have hS : mathieuSpecA m q = mathieuSpecA n q := by simp [mathieuSpecA, hm, hn]
    rw [hS, hmn, hn2] at hm2
    have : (n / 2 : ℕ) = m / 2 := by exact_mod_cast hm2
    obtain ⟨i, rfl⟩ := hm; obtain ⟨j, rfl⟩ := hn; omega
  · simp only [mathieuSpecA, hm, ↓reduceIte, Set.mem_ofPred_eq] at hm1
    simp only [mathieuSpecA, Nat.not_even_iff_odd.mpr hn, ↓reduceIte, Set.mem_ofPred_eq] at hn1
    rw [← hmn] at hn1
    rw [hm1, hn1] at hW; simp at hW
  · simp only [mathieuSpecA, Nat.not_even_iff_odd.mpr hm, ↓reduceIte, Set.mem_ofPred_eq] at hm1
    simp only [mathieuSpecA, hn, ↓reduceIte, Set.mem_ofPred_eq] at hn1
    rw [← hmn] at hn1
    rw [hm1, hn1] at hW; simp at hW
  · have hS : mathieuSpecA m q = mathieuSpecA n q := by
      simp [mathieuSpecA, Nat.not_even_iff_odd.mpr hm, Nat.not_even_iff_odd.mpr hn]
    rw [hS, hmn, hn2] at hm2
    have : (n / 2 : ℕ) = m / 2 := by exact_mod_cast hm2
    obtain ⟨i, rfl⟩ := hm; obtain ⟨j, rfl⟩ := hn; omega

/-- The eigenvalues `b_n(q)`, `n ≥ 1`, are pairwise distinct. -/
lemma p1a1_mathieuB_injective {m n : ℕ} (hm0 : m ≠ 0) (hn0 : n ≠ 0) (q : ℝ)
    (hmn : mathieuB m q = mathieuB n q) : m = n := by
  have hW := mathieuWI_wronskian (mathieuB m q) q (π / 2)
  obtain ⟨hm1, hm2⟩ := mathieuB_spec hm0 q
  obtain ⟨hn1, hn2⟩ := mathieuB_spec hn0 q
  rcases Nat.even_or_odd m with hm | hm <;> rcases Nat.even_or_odd n with hn | hn
  · have hS : mathieuSpecB m q = mathieuSpecB n q := by simp [mathieuSpecB, hm, hn]
    rw [hS, hmn, hn2] at hm2
    have : ((n - 1) / 2 : ℕ) = (m - 1) / 2 := by exact_mod_cast hm2
    obtain ⟨i, rfl⟩ := hm; obtain ⟨j, rfl⟩ := hn; omega
  · simp only [mathieuSpecB, hm, ↓reduceIte, Set.mem_ofPred_eq] at hm1
    simp only [mathieuSpecB, Nat.not_even_iff_odd.mpr hn, ↓reduceIte, Set.mem_ofPred_eq] at hn1
    rw [← hmn] at hn1
    rw [hm1, hn1] at hW; simp at hW
  · simp only [mathieuSpecB, Nat.not_even_iff_odd.mpr hm, ↓reduceIte, Set.mem_ofPred_eq] at hm1
    simp only [mathieuSpecB, hn, ↓reduceIte, Set.mem_ofPred_eq] at hn1
    rw [← hmn] at hn1
    rw [hm1, hn1] at hW; simp at hW
  · have hS : mathieuSpecB m q = mathieuSpecB n q := by
      simp [mathieuSpecB, Nat.not_even_iff_odd.mpr hm, Nat.not_even_iff_odd.mpr hn]
    rw [hS, hmn, hn2] at hm2
    have : ((n - 1) / 2 : ℕ) = (m - 1) / 2 := by exact_mod_cast hm2
    obtain ⟨i, rfl⟩ := hm; obtain ⟨j, rfl⟩ := hn; omega

/-! ### The case `q = 0` -/

/-- Derivative of `cos(sz)`. -/
theorem p1a1_hasDerivAt_cos_mul (s z : ℂ) :
    HasDerivAt (fun z => Complex.cos (s * z)) (-Complex.sin (s * z) * s) z := by
  have := ((hasDerivAt_id' z).const_mul s).ccos
  convert this using 1; ring

/-- Derivative of `sin(sz)/s`. -/
lemma p1a1_hasDerivAt_sin_mul_div {s : ℂ} (hs0 : s ≠ 0) (z : ℂ) :
    HasDerivAt (fun z => Complex.sin (s * z) / s) (Complex.cos (s * z)) z := by
  have := (((hasDerivAt_id' z).const_mul s).csin).div_const s
  convert this using 1; field_simp

/-- `w_I(z; a, 0) = cos(sz)` for any `s` with `s² = a`. -/
theorem p1a1_mathieuWI_q_zero {a s : ℂ} (hs : s ^ 2 = a) (z : ℂ) :
    mathieuWI a 0 z = Complex.cos (s * z) := by
  obtain ⟨h, h0, h1⟩ := mathieuWI_spec a 0
  have hdd : ∀ z, HasDerivAt (fun z => -Complex.sin (s * z) * s)
      (-(Complex.cos (s * z) * s) * s) z := fun z => by
    have := (((hasDerivAt_id' z).const_mul s).csin).neg.mul_const s
    convert this using 1; ring
  have hc : IsMathieuSolution a 0 (fun z => Complex.cos (s * z)) := by
    refine ⟨fun z => (p1a1_hasDerivAt_cos_mul s z).differentiableAt, fun z => ?_⟩
    rw [show deriv (fun z => Complex.cos (s * z)) = fun z => -Complex.sin (s * z) * s from
      funext fun z => (p1a1_hasDerivAt_cos_mul s z).deriv]
    convert hdd z using 1; rw [← hs]; ring
  have := h.eq_of_initial hc (z₀ := 0) (by simp [h0])
    (by rw [h1, (p1a1_hasDerivAt_cos_mul s 0).deriv]; simp)
  exact congrFun this z

/-- `w_II(z; a, 0) = sin(sz)/s` for any `s ≠ 0` with `s² = a`. -/
theorem p1a1_mathieuWII_q_zero {a s : ℂ} (hs : s ^ 2 = a) (hs0 : s ≠ 0) (z : ℂ) :
    mathieuWII a 0 z = Complex.sin (s * z) / s := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec a 0
  have hc : IsMathieuSolution a 0 (fun z => Complex.sin (s * z) / s) := by
    refine ⟨fun z => (p1a1_hasDerivAt_sin_mul_div hs0 z).differentiableAt, fun z => ?_⟩
    rw [show deriv (fun z => Complex.sin (s * z) / s) = fun z => Complex.cos (s * z) from
      funext fun z => (p1a1_hasDerivAt_sin_mul_div hs0 z).deriv]
    convert p1a1_hasDerivAt_cos_mul s z using 1; rw [← hs]; field_simp; ring
  have := h.eq_of_initial hc (z₀ := 0) (by simp [h0])
    (by rw [h1, (p1a1_hasDerivAt_sin_mul_div hs0 0).deriv]; simp)
  exact congrFun this z

/-- `w_II(z; 0, 0) = z`. -/
theorem p1a1_mathieuWII_zero_zero (z : ℂ) : mathieuWII 0 0 z = z := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec 0 0
  have hc : IsMathieuSolution 0 0 (fun z => z) := by
    refine ⟨differentiable_id, fun z => ?_⟩
    rw [show deriv (fun z : ℂ => z) = fun _ => 1 from funext fun z => deriv_id z]
    simpa using hasDerivAt_const z (1 : ℂ)
  have := h.eq_of_initial hc (z₀ := 0) (by simp [h0]) (by rw [h1]; simp)
  exact congrFun this z

/-- `deriv w_I(·; s², 0) = -s sin(s ·)`. -/
theorem p1a1_deriv_mathieuWI_q_zero {a s : ℂ} (hs : s ^ 2 = a) (z : ℂ) :
    deriv (mathieuWI a 0) z = -Complex.sin (s * z) * s := by
  rw [show mathieuWI a 0 = fun z => Complex.cos (s * z) from funext (p1a1_mathieuWI_q_zero hs)]
  exact (p1a1_hasDerivAt_cos_mul s z).deriv

/-- `deriv w_II(·; s², 0) = cos(s ·)`, `s ≠ 0`. -/
theorem p1a1_deriv_mathieuWII_q_zero {a s : ℂ} (hs : s ^ 2 = a) (hs0 : s ≠ 0) (z : ℂ) :
    deriv (mathieuWII a 0) z = Complex.cos (s * z) := by
  rw [show mathieuWII a 0 = fun z => Complex.sin (s * z) / s from
    funext (p1a1_mathieuWII_q_zero hs hs0)]
  exact (p1a1_hasDerivAt_sin_mul_div hs0 z).deriv

/-- The `n`-th smallest element of the range of a strictly increasing sequence. -/
lemma p1a1_nthLeast_range {f : ℕ → ℝ} (hf : StrictMono f) (n : ℕ) :
    nthLeast (range f) n = f n := by
  apply nthLeast_eq_of (Set.mem_range_self n)
  have e : range f ∩ Iio (f n) = f '' (Iio n) := by
    ext x; constructor
    · rintro ⟨⟨k, rfl⟩, hk⟩; exact Set.mem_image_of_mem f (hf.lt_iff_lt.mp hk)
    · rintro ⟨k, hk, rfl⟩; exact ⟨Set.mem_range_self k, hf (Set.mem_Iio.mp hk)⟩
  rw [e, hf.injective.injOn.encard_image]
  simp [Set.encard_eq_coe_toFinset_card]

/-- `s` with `s ⋅ π/2 = m π` is `2m`. -/
lemma p1a1_eq_two_mul_of_sin {s : ℂ} (h : Complex.sin (s * (π / 2)) = 0) :
    ∃ m : ℤ, s = 2 * m := by
  obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp h
  refine ⟨m, ?_⟩
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_right_cancel₀ hπ; linear_combination 2 * hm

/-- `s` with `cos(s ⋅ π/2) = 0` is `2m + 1`. -/
lemma p1a1_eq_two_mul_add_one_of_cos {s : ℂ} (h : Complex.cos (s * (π / 2)) = 0) :
    ∃ m : ℤ, s = 2 * m + 1 := by
  obtain ⟨m, hm⟩ := Complex.cos_eq_zero_iff.mp h
  refine ⟨m, ?_⟩
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_right_cancel₀ hπ; linear_combination 2 * hm

/-- `|m|² = m²` in `ℂ`. -/
lemma p1a1_natAbs_sq (m : ℤ) : ((m.natAbs : ℕ) : ℂ) ^ 2 = (m : ℂ) ^ 2 := by
  have := congrArg (fun t : ℤ => (t : ℂ)) (Int.natAbs_sq m)
  simpa only [Int.cast_pow, Int.cast_natCast] using this

/-- An odd integer squared is `(2j+1)²` for a natural `j`. -/
lemma p1a1_odd_sq (m : ℤ) : ∃ j : ℕ, ((2 * m + 1 : ℂ)) ^ 2 = ((2 * j + 1 : ℕ) : ℂ) ^ 2 := by
  rcases le_or_gt 0 m with hm | hm
  · refine ⟨m.toNat, ?_⟩
    have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
    have h2 : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by exact_mod_cast this
    push_cast; rw [h2]
  · refine ⟨(-m - 1).toNat, ?_⟩
    have : (((-m - 1).toNat : ℕ) : ℤ) = -m - 1 := Int.toNat_of_nonneg (by omega)
    have h2 : (((-m - 1).toNat : ℕ) : ℂ) = ((-m - 1 : ℤ) : ℂ) := by exact_mod_cast this
    push_cast; rw [h2]; push_cast; ring

/-- The spectrum of the `a_{2k}` at `q = 0` is `{(2j)²}`. -/
lemma p1a1_specA_even_zero (k : ℕ) :
    mathieuSpecA (2 * k) 0 = range fun j : ℕ => ((2 * j : ℕ) : ℝ) ^ 2 := by
  ext a
  simp only [mathieuSpecA, show Even (2 * k) from even_two_mul k, ↓reduceIte,
    Set.mem_ofPred_eq, mem_range, Complex.ofReal_zero]
  constructor
  · intro h
    set s := Complex.sqrt a
    have hs : s ^ 2 = a := DLMF.Elementary.trig_sqrt_sq _
    rw [p1a1_deriv_mathieuWI_q_zero hs] at h
    obtain ⟨m, hm⟩ : ∃ m : ℤ, s = 2 * m := by
      rcases mul_eq_zero.mp h with h | h
      · exact p1a1_eq_two_mul_of_sin (by simpa using h)
      · exact ⟨0, by simp [h]⟩
    refine ⟨m.natAbs, ?_⟩
    have : ((a : ℝ) : ℂ) = ((((2 * m.natAbs : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hs, hm]; push_cast; rw [mul_pow, mul_pow, p1a1_natAbs_sq]
    exact_mod_cast this.symm
  · rintro ⟨j, rfl⟩
    have hs : ((2 * j : ℕ) : ℂ) ^ 2 = (((((2 * j : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [p1a1_deriv_mathieuWI_q_zero hs]
    have : Complex.sin (((2 * j : ℕ) : ℂ) * (π / 2)) = 0 := by
      rw [Complex.sin_eq_zero_iff]; exact ⟨j, by push_cast; ring⟩
    rw [this]; simp

/-- The spectrum of the `a_{2k+1}` at `q = 0` is `{(2j+1)²}`. -/
lemma p1a1_specA_odd_zero (k : ℕ) :
    mathieuSpecA (2 * k + 1) 0 = range fun j : ℕ => ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
  ext a
  simp only [mathieuSpecA, Nat.not_even_bit1, ↓reduceIte,
    Set.mem_ofPred_eq, mem_range, Complex.ofReal_zero]
  constructor
  · intro h
    set s := Complex.sqrt a
    have hs : s ^ 2 = a := DLMF.Elementary.trig_sqrt_sq _
    rw [p1a1_mathieuWI_q_zero hs] at h
    obtain ⟨m, hm⟩ := p1a1_eq_two_mul_add_one_of_cos h
    obtain ⟨j, hj⟩ := p1a1_odd_sq m
    refine ⟨j, ?_⟩
    have : ((a : ℝ) : ℂ) = ((((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hs, hm, hj]; push_cast; ring
    exact_mod_cast this.symm
  · rintro ⟨j, rfl⟩
    have hs : ((2 * j + 1 : ℕ) : ℂ) ^ 2 = (((((2 * j + 1 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [p1a1_mathieuWI_q_zero hs, Complex.cos_eq_zero_iff]
    exact ⟨j, by push_cast; ring⟩

/-- The spectrum of the `b_{2k+1}` at `q = 0` is `{(2j+1)²}`. -/
lemma p1a1_specB_odd_zero (k : ℕ) :
    mathieuSpecB (2 * k + 1) 0 = range fun j : ℕ => ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
  ext a
  simp only [mathieuSpecB, Nat.not_even_bit1, ↓reduceIte,
    Set.mem_ofPred_eq, mem_range, Complex.ofReal_zero]
  constructor
  · intro h
    set s := Complex.sqrt a
    have hs : s ^ 2 = a := DLMF.Elementary.trig_sqrt_sq _
    rcases eq_or_ne s 0 with hs0 | hs0
    · exfalso
      have ha : (a : ℂ) = 0 := by rw [← hs, hs0]; ring
      rw [ha] at h
      rw [show mathieuWII 0 0 = fun z => z from funext p1a1_mathieuWII_zero_zero] at h
      simp at h
    rw [p1a1_deriv_mathieuWII_q_zero hs hs0] at h
    obtain ⟨m, hm⟩ := p1a1_eq_two_mul_add_one_of_cos h
    obtain ⟨j, hj⟩ := p1a1_odd_sq m
    refine ⟨j, ?_⟩
    have : ((a : ℝ) : ℂ) = ((((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hs, hm, hj]; push_cast; ring
    exact_mod_cast this.symm
  · rintro ⟨j, rfl⟩
    have hs : ((2 * j + 1 : ℕ) : ℂ) ^ 2 = (((((2 * j + 1 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [p1a1_deriv_mathieuWII_q_zero hs (Nat.cast_ne_zero.mpr (by omega)), Complex.cos_eq_zero_iff]
    exact ⟨j, by push_cast; ring⟩

/-- The spectrum of the `b_{2k+2}` at `q = 0` is `{(2j+2)²}`. -/
lemma p1a1_specB_even_zero (k : ℕ) :
    mathieuSpecB (2 * k + 2) 0 = range fun j : ℕ => ((2 * j + 2 : ℕ) : ℝ) ^ 2 := by
  ext a
  have he : Even (2 * k + 2) := ⟨k + 1, by ring⟩
  simp only [mathieuSpecB, he, ↓reduceIte, Set.mem_ofPred_eq, mem_range, Complex.ofReal_zero]
  constructor
  · intro h
    set s := Complex.sqrt a
    have hs : s ^ 2 = a := DLMF.Elementary.trig_sqrt_sq _
    rcases eq_or_ne s 0 with hs0 | hs0
    · exfalso
      have ha : (a : ℂ) = 0 := by rw [← hs, hs0]; ring
      rw [ha, p1a1_mathieuWII_zero_zero] at h
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact hπ (by linear_combination 2 * h)
    rw [p1a1_mathieuWII_q_zero hs hs0, div_eq_zero_iff, or_iff_left hs0] at h
    obtain ⟨m, hm⟩ := p1a1_eq_two_mul_of_sin h
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hs0 hm
    refine ⟨m.natAbs - 1, ?_⟩
    have hna : ((m.natAbs - 1 : ℕ) : ℂ) = (m.natAbs : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have : ((a : ℝ) : ℂ) = ((((2 * (m.natAbs - 1) + 2 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hs, hm]; push_cast; rw [hna]
      linear_combination (-4 : ℂ) * p1a1_natAbs_sq m
    exact_mod_cast this.symm
  · rintro ⟨j, rfl⟩
    have hs : ((2 * j + 2 : ℕ) : ℂ) ^ 2 = (((((2 * j + 2 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [p1a1_mathieuWII_q_zero hs (Nat.cast_ne_zero.mpr (by omega))]
    have : Complex.sin (((2 * j + 2 : ℕ) : ℂ) * (π / 2)) = 0 := by
      rw [Complex.sin_eq_zero_iff]; exact ⟨j + 1, by push_cast; ring⟩
    rw [this, zero_div]

/-- **DLMF 28.2.23**: `a_n(0) = n²`, `n = 0, 1, 2, …`. -/
@[dlmf 28.2.E23]
theorem mathieuA_zero (n : ℕ) : mathieuA n 0 = (n : ℝ) ^ 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [mathieuA, p1a1_specA_even_zero, show 2 * k / 2 = k by omega,
      p1a1_nthLeast_range (by intro i j h; simp only; gcongr)]
  · rw [mathieuA, p1a1_specA_odd_zero, show (2 * k + 1) / 2 = k by omega,
      p1a1_nthLeast_range (by intro i j h; simp only; gcongr)]

/-- **DLMF 28.2.24**: `b_n(0) = n²`, `n = 1, 2, 3, …`. -/
@[dlmf 28.2.E24]
theorem mathieuB_zero {n : ℕ} (hn : n ≠ 0) : mathieuB n 0 = (n : ℝ) ^ 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [mathieuB, hn, ↓reduceIte]
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, p1a1_specB_even_zero,
      show (2 * j + 2 - 1) / 2 = j by omega,
      p1a1_nthLeast_range (by intro i j h; simp only; gcongr)]
  · simp only [mathieuB, hn, ↓reduceIte]
    rw [p1a1_specB_odd_zero, show (2 * k + 1 - 1) / 2 = k by omega,
      p1a1_nthLeast_range (by intro i j h; simp only; gcongr)]

/-- **Distribution of the eigenvalues** (DLMF 28.2.25), `q > 0`:
`a_0 < b_1 < a_1 < b_2 < a_2 < b_3 < ⋯`. -/
@[dlmf 28.2.E25]
theorem mathieu_eigenvalues_interlace_pos {q : ℝ} (hq : 0 < q) (n : ℕ) :
    mathieuA n q < mathieuB (n + 1) q ∧ mathieuB (n + 1) q < mathieuA (n + 1) q := by
  sorry

/-- **Distribution of the eigenvalues** (DLMF 28.2.25), `q < 0`:
`a_0 < a_1 < b_1 < b_2 < a_2 < a_3 < b_3 < b_4 < ⋯`. -/
@[dlmf 28.2.E25]
theorem mathieu_eigenvalues_interlace_neg {q : ℝ} (hq : q < 0) (n : ℕ) :
    mathieuA (2 * n) q < mathieuA (2 * n + 1) q ∧
      mathieuA (2 * n + 1) q < mathieuB (2 * n + 1) q ∧
      mathieuB (2 * n + 1) q < mathieuB (2 * n + 2) q ∧
      mathieuB (2 * n + 2) q < mathieuA (2 * n + 2) q := by
  sorry

/-- **DLMF 28.2.26**: `a_{2n}(-q) = a_{2n}(q)`. -/
@[dlmf 28.2.E26]
theorem mathieuA_even_neg (n : ℕ) (q : ℝ) : mathieuA (2 * n) (-q) = mathieuA (2 * n) q := by
  have hS : mathieuSpecA (2 * n) (-q) = mathieuSpecA (2 * n) q := by
    ext a
    simp [mathieuSpecA, p1a1_deriv_mathieuWI_half_pi_neg_q]
  simp only [mathieuA, hS]

/-- **DLMF 28.2.27**: `a_{2n+1}(-q) = b_{2n+1}(q)`. -/
@[dlmf 28.2.E27]
theorem mathieuA_odd_neg (n : ℕ) (q : ℝ) :
    mathieuA (2 * n + 1) (-q) = mathieuB (2 * n + 1) q := by
  have hS : mathieuSpecA (2 * n + 1) (-q) = mathieuSpecB (2 * n + 1) q := by
    ext a
    simp [mathieuSpecA, mathieuSpecB, Nat.not_even_bit1, p1a1_mathieuWI_half_pi_neg_q]
  simp only [mathieuA, mathieuB, hS, show 2 * n + 1 ≠ 0 by omega, ite_false,
    show (2 * n + 1) / 2 = (2 * n + 1 - 1) / 2 by omega]

/-- **DLMF 28.2.28**: `b_{2n+2}(-q) = b_{2n+2}(q)`. -/
@[dlmf 28.2.E28]
theorem mathieuB_even_neg (n : ℕ) (q : ℝ) :
    mathieuB (2 * n + 2) (-q) = mathieuB (2 * n + 2) q := by
  have hS : mathieuSpecB (2 * n + 2) (-q) = mathieuSpecB (2 * n + 2) q := by
    ext a
    have he : Even (2 * n + 2) := ⟨n + 1, by ring⟩
    simp [mathieuSpecB, he, p1a1_mathieuWII_half_pi_neg_q]
  simp only [mathieuB, hS]

end DLMF.Mathieu
end
