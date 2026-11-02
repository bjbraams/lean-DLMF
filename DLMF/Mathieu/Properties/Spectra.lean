/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Properties.Floquet
public import DLMF.Mathieu.Hill.Floquet

/-!
# Mathieu characteristic spectra

This file treats the eigenvalues `a_n(q)`, `b_n(q)` of Mathieu's equation (DLMF §28.2(v)): the
boundary conditions at `π/2`, the characterizations of Table 28.2.1, the ordering within and
between the spectra, the values at `q = 0` and the relations between `q` and `-q`.

## Main results

* `charExp_set_infinite_discrete`: for given `ν` and `q` the roots `a` of the characteristic
  equation 28.2.16 form an infinite discrete set (DLMF §28.2(v)).
* `deriv_mathieuWI_half_pi_mathieuA_even`, `mathieuWI_half_pi_mathieuA_odd`: DLMF 28.2.21.
* `deriv_mathieuWII_half_pi_mathieuB_odd`, `mathieuWII_half_pi_mathieuB_even`: DLMF 28.2.22.
* `exists_solution_neumann_iff`, `exists_solution_neumann_dirichlet_iff`,
  `exists_solution_dirichlet_neumann_iff`, `exists_solution_dirichlet_iff`: Table 28.2.1.
* `mathieuA_lt_mathieuA_add_two`, `mathieuB_lt_mathieuB_add_two`: the ordering within each
  spectrum (DLMF §28.2(v)).
* `mathieuA_zero`, `mathieuB_zero`: `a_n(0) = n²`, `b_n(0) = n²` (DLMF 28.2.23, 28.2.24).
* `mathieu_eigenvalues_interlace_pos`, `mathieu_eigenvalues_interlace_neg`: the distribution of
  the eigenvalues for `q > 0` and `q < 0` (DLMF 28.2.25).
* `mathieuA_even_neg`, `mathieuA_odd_neg`, `mathieuB_even_neg`: DLMF 28.2.26–28.2.28.
-/

@[expose] public noncomputable section

open Complex Set Filter ComplexConjugate

open scoped Topology Real

namespace DLMF.Mathieu

/-! ### Eigenvalues (§28.2(v)) -/

/-- The restriction of a solution of Mathieu's equation to the real axis, as a first-order
system. -/
private lemma IsMathieuSolution.hasDerivAt_ofReal {a q : ℂ} {w : ℂ → ℂ}
    (hw : IsMathieuSolution a q w) (x : ℝ) :
    HasDerivAt (fun x : ℝ => w x) (deriv w x) x ∧
      HasDerivAt (fun x : ℝ => deriv w x)
        (-(a + -2 * q * Complex.cos (2 * (x : ℂ))) * w x) x := by
  refine ⟨((hw.differentiable x).hasDerivAt).comp_ofReal, ?_⟩
  exact ((hw.hasDerivAt_deriv x).comp_ofReal).congr_deriv (by ring)

/-- `‖cos 2x‖ ≤ 1` for real `x`. -/
private lemma norm_cos_two_mul_ofReal_le (x : ℝ) : ‖Complex.cos (2 * (x : ℂ))‖ ≤ 1 := by
  rw [show (2 * (x : ℂ)) = ((2 * x : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cos,
    Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

/-- Growth of `w_I(π; a, q)` in `a`: `‖w_I(π; a, q)‖ ≤ e^{‖q‖π} e^{π ‖a‖^{1/2}}` for
`‖a‖ ≥ 1`. -/
private lemma norm_mathieuWI_pi_le (q : ℂ) {a : ℂ} (ha : 1 ≤ ‖a‖) :
    ‖mathieuWI a q π‖ ≤ Real.exp (‖q‖ * π) * Real.exp (π * Real.sqrt ‖a‖) := by
  set k := Real.sqrt ‖a‖
  set M := 2 * ‖q‖
  have hM : 0 ≤ M := by positivity
  have hk : 1 ≤ k := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt ha
  have hk2 : k ^ 2 = ‖a‖ := Real.sq_sqrt (by linarith)
  have hw := isMathieuSolution_mathieuWI a q
  have hP : ∀ x ∈ Icc 0 π, ‖-(a + -2 * q * Complex.cos (2 * (x : ℂ)))‖ ≤ M + k ^ 2 := by
    intro x _
    rw [norm_neg, hk2]
    calc ‖a + -2 * q * Complex.cos (2 * (x : ℂ))‖ ≤ ‖a‖ + 2 * ‖q‖ * 1 := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_neg]
          gcongr
          · simp
          · exact norm_cos_two_mul_ofReal_le x
      _ = M + ‖a‖ := by ring
  have hπ : π ∈ Icc 0 π := ⟨Real.pi_pos.le, le_rfl⟩
  have e := ODE.norm_deriv_sq_add_sq_mul_norm_sq_le_exp hM hk hP
    (fun x => (hw.hasDerivAt_ofReal x).1) (fun x => (hw.hasDerivAt_ofReal x).2) hπ
  simp only [ofReal_zero, mathieuWI_apply_zero, deriv_mathieuWI_apply_zero, norm_zero,
    norm_one] at e
  have hB : Real.exp ((M + 2 * k) * π) =
      (Real.exp (‖q‖ * π) * Real.exp (π * k)) ^ 2 := by
    rw [← Real.exp_add, sq, ← Real.exp_add]; simp only [M]; ring_nf
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [← hB]
  have hk2' : 0 < k ^ 2 := by positivity
  have : k ^ 2 * ‖mathieuWI a q π‖ ^ 2 ≤ k ^ 2 * Real.exp ((M + 2 * k) * π) := by
    nlinarith [sq_nonneg ‖deriv (mathieuWI a q) (π : ℂ)‖]
  exact le_of_mul_le_mul_left this hk2'

/-- **Discrete set of eigenvalues** (DLMF §28.2(v)): for given `ν` and `q`, the set of `a`
satisfying the characteristic equation 28.2.16 is infinite and has no finite accumulation
point. -/
@[dlmf 28.2.v]
theorem charExp_set_infinite_discrete (q ν : ℂ) :
    {a : ℂ | IsMathieuCharExp a q ν}.Infinite ∧
      ∀ K : Set ℂ, IsCompact K → (K ∩ {a : ℂ | IsMathieuCharExp a q ν}).Finite := by
  set D : ℂ → ℂ := fun a => 2 * mathieuWI a q π
  have hD : Differentiable ℂ D := by
    have h := differentiable_mathieuWI_mathieuWII.1
    have : Differentiable ℂ fun a : ℂ => ((π : ℂ), a, q) := by fun_prop
    exact (h.comp this).const_mul 2
  -- growth
  have hgrowth : ∀ z, max 1 (π ^ 4) ≤ ‖z‖ →
      ‖D z‖ ≤ 2 * Real.exp (‖q‖ * π) * Real.exp (‖z‖ ^ ((3 : ℝ) / 4)) := by
    intro z hz
    have h1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hz
    have hr : 0 < ‖z‖ := by linarith
    simp only [D, norm_mul, Complex.norm_ofNat, mul_assoc]
    gcongr
    refine (norm_mathieuWI_pi_le q h1).trans ?_
    gcongr
    have hpi : π ≤ ‖z‖ ^ ((1 : ℝ) / 4) := by
      calc π = (π ^ 4) ^ ((1 : ℝ) / 4) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]; norm_num
        _ ≤ ‖z‖ ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity)
            ((le_max_right _ _).trans hz) (by norm_num)
    rw [show ((3 : ℝ) / 4) = 1 / 4 + 1 / 2 by norm_num, Real.rpow_add hr, Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_right hpi (by positivity)
  -- asymptotics on the positive axis
  have hlim : Tendsto (fun k : ℝ => D ((k : ℂ) ^ 2) - 2 * Real.cos (k * Real.pi)) atTop
      (𝓝 0) := by
    set M := 2 * ‖q‖
    have hM : 0 ≤ M := by positivity
    set B := M * Real.exp ((M + 1) * Real.pi / 2)
    have hB : 0 ≤ B := by positivity
    have hB2 : B ^ 2 = M ^ 2 * Real.exp ((M + 1) * Real.pi) := by
      simp only [B]; rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    have hπ : Real.pi ∈ Icc 0 Real.pi := ⟨Real.pi_pos.le, le_rfl⟩
    have hQ : ∀ x ∈ Icc 0 Real.pi, ‖-2 * q * Complex.cos (2 * (x : ℂ))‖ ≤ M := by
      intro x _
      rw [norm_mul, norm_mul, norm_neg]
      simp only [Complex.norm_ofNat, M]
      nlinarith [norm_cos_two_mul_ofReal_le x, norm_nonneg q]
    have key : ∀ k : ℝ, 1 ≤ k →
        ‖D ((k : ℂ) ^ 2) - 2 * Real.cos (k * Real.pi)‖ ≤ 2 * B / k := by
      intro k hk
      have hk0 : 0 < k := by linarith
      have hw := isMathieuSolution_mathieuWI ((k : ℂ) ^ 2) q
      have e := ODE.energy_sub_harmonic_le (Q := fun x : ℝ => -2 * q * Complex.cos (2 * (x : ℂ)))
        (a := 1) (b := 0) hM hk hQ (fun x => (hw.hasDerivAt_ofReal x).1)
        (fun x => ((hw.hasDerivAt_ofReal x).2).congr_deriv (by ring))
        (by simpa using mathieuWI_apply_zero ((k : ℂ) ^ 2) q)
        (by simpa using deriv_mathieuWI_apply_zero ((k : ℂ) ^ 2) q) hπ
      simp only [norm_one, norm_zero, one_mul, zero_mul, one_pow, zero_add, add_zero,
        zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one] at e
      have hk2 : 0 < k ^ 2 := by positivity
      rw [show M ^ 2 * k ^ 2 * Real.exp ((M + 1) * Real.pi) / k ^ 2 =
        M ^ 2 * Real.exp ((M + 1) * Real.pi) by field_simp] at e
      have h1 : ‖mathieuWI ((k : ℂ) ^ 2) q π - Real.cos (k * Real.pi)‖ ≤ B / k := by
        refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
        rw [div_pow, hB2, le_div_iff₀ hk2]
        nlinarith [sq_nonneg ‖deriv (mathieuWI ((k : ℂ) ^ 2) q) (Real.pi : ℂ) -
          -(k * Real.sin (k * Real.pi) : ℂ)‖]
      calc ‖D ((k : ℂ) ^ 2) - 2 * Real.cos (k * Real.pi)‖ =
            2 * ‖mathieuWI ((k : ℂ) ^ 2) q π - Real.cos (k * Real.pi)‖ := by
            simp only [D]
            rw [← mul_sub, norm_mul, Complex.norm_ofNat]
        _ ≤ 2 * (B / k) := by gcongr
        _ = 2 * B / k := by ring
    refine squeeze_zero_norm' (eventually_atTop.2 ⟨1, key⟩) ?_
    exact tendsto_const_nhds.div_atTop tendsto_id
  have hinf := setOf_eq_infinite_of_tendsto_sub_two_cos hD (by norm_num) (by norm_num)
    hgrowth hlim
  have hset : {a : ℂ | IsMathieuCharExp a q ν} = {a | D a = 2 * Complex.cos (π * ν)} := by
    ext a
    simp only [IsMathieuCharExp, mem_ofPred_eq, D]
    constructor
    · intro h; linear_combination -2 * h
    · intro h; linear_combination -h / 2
  refine ⟨hset ▸ hinf _, fun K hK => ?_⟩
  by_contra hfin
  obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact
    (s := K ∩ {a | IsMathieuCharExp a q ν}) hfin hK inter_subset_left
  have hfreq : ∃ᶠ z in 𝓝[≠] x, D z - 2 * Complex.cos (π * ν) = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hx
    refine hx.mono fun z hz => ?_
    have := hz.2
    rw [hset] at this
    exact sub_eq_zero.mpr this
  have han : AnalyticOnNhd ℂ (fun z => D z - 2 * Complex.cos (π * ν)) univ := fun z _ =>
    (hD.sub_const (2 * Complex.cos (π * ν))).analyticAt z
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ x) hfreq
  obtain ⟨z, hz⟩ := (hinf (2 * Complex.cos (π * ν) + 1)).nonempty
  have := hzero (mem_univ z)
  simp only [Pi.zero_apply, mem_ofPred_eq] at this hz
  rw [hz] at this
  norm_num at this

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
private lemma finite_real_zeros_Icc {g : ℂ → ℂ} (hg : Differentiable ℂ g) {y : ℝ} (hy : g y ≠ 0)
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
private lemma finite_inter_Iio_of_zeros {S : Set ℝ} {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hSg : ∀ x ∈ S, g x = 0) {x₀ : ℝ} (hx₀ : ∀ y ∈ S, x₀ ≤ y) {y : ℝ} (hy : g y ≠ 0) (a : ℝ) :
    (S ∩ Iio a).Finite :=
  (finite_real_zeros_Icc hg hy x₀ a).subset fun x hx =>
    ⟨⟨hx₀ x hx.1, (Set.mem_Iio.mp hx.2).le⟩, hSg x hx.1⟩

/-- An element of `S` with finitely many smaller elements is some `nthLeast S k`. -/
theorem exists_eq_nthLeast {S : Set ℝ} {a : ℝ} (ha : a ∈ S) (hfin : (S ∩ Iio a).Finite) :
    ∃ k : ℕ, a = nthLeast S k :=
  ⟨(S ∩ Iio a).ncard, (nthLeast_eq_of ha hfin.cast_ncard_eq.symm).symm⟩

/-- The least element of a spectrum. -/
private lemma le_of_encard_inter_Iio_eq_zero {S : Set ℝ} {x₀ : ℝ}
    (h : (S ∩ Iio x₀).encard = (0 : ℕ)) :
    ∀ y ∈ S, x₀ ≤ y := by
  intro y hy
  by_contra hlt
  rw [not_le] at hlt
  have : (S ∩ Iio x₀) = ∅ := by exact_mod_cast Set.encard_eq_zero.mp (by exact_mod_cast h)
  exact (Set.eq_empty_iff_forall_notMem.mp this) y ⟨hy, hlt⟩

/-- `a ↦ w_I(z; a, q)` and `a ↦ w_II(z; a, q)` are entire (from 28.2(ii)). -/
private lemma differentiable_mathieuWI_mathieuWII_a (z q : ℂ) :
    Differentiable ℂ (fun a => mathieuWI a q z) ∧ Differentiable ℂ (fun a => mathieuWII a q z) := by
  have hl : Differentiable ℂ (fun a : ℂ => (z, a, q)) := by fun_prop
  exact ⟨differentiable_mathieuWI_mathieuWII.1.comp hl,
    differentiable_mathieuWI_mathieuWII.2.comp hl⟩

/-- A spectrum with an element having no smaller elements is bounded below. -/
private lemma exists_lower_bound_of_encard_inter_Iio_eq_zero (S : Set ℝ)
    (h : ∃ x ∈ S, (S ∩ Iio x).encard = (0 : ℕ)) :
    ∃ x₀, ∀ y ∈ S, x₀ ≤ y := by
  obtain ⟨x, -, hx⟩ := h; exact ⟨x, le_of_encard_inter_Iio_eq_zero hx⟩

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
      have := hw.deriv_eq_mathieuWI_mathieuWII (π / 2)
      rw [h0, zero_mul, add_zero, h1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hw0
    set S := mathieuSpecA 0 q
    have hS : ∀ k, mathieuSpecA (2 * k) q = S := by
      intro k; simp [S, mathieuSpecA]
    have haS : a ∈ S := by simpa [S, mathieuSpecA] using hA'
    obtain ⟨x₀, hx₀⟩ := exists_lower_bound_of_encard_inter_Iio_eq_zero S (mathieuSpecA_exists 0 q 0)
    obtain ⟨y₀, hy₀⟩ := exists_lower_bound_of_encard_inter_Iio_eq_zero (mathieuSpecB 2 q)
        (mathieuSpecB_exists 2 q 0)
    have hfin : (S ∩ Iio a).Finite := by
      refine finite_inter_Iio_of_zeros (g := fun b => mathieuWI b q π - 1)
        ((differentiable_mathieuWI_mathieuWII_a _ _).1.sub_const 1) (fun x hx => ?_) hx₀
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
    obtain ⟨k, hk⟩ := exists_eq_nthLeast haS hfin
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
    obtain ⟨x₀, hx₀⟩ := exists_lower_bound_of_encard_inter_Iio_eq_zero S (mathieuSpecA_exists 1 q 0)
    have hfin : (S ∩ Iio a).Finite := by
      refine finite_inter_Iio_of_zeros (g := fun b => mathieuWI b q (π / 2))
        (differentiable_mathieuWI_mathieuWII_a _ _).1 (fun x hx => (hmem x).mp hx) hx₀
        (y := x₀ - 1) (fun h0 => ?_) a
      have := hx₀ _ ((hmem _).mpr h0); linarith
    obtain ⟨k, hk⟩ := exists_eq_nthLeast ((hmem a).mpr hA) hfin
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
      have := hw.deriv_eq_mathieuWI_mathieuWII (π / 2)
      rw [h0, zero_mul, zero_add, h1] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hw0
    set S := mathieuSpecB 1 q
    have hS : ∀ k, mathieuSpecB (2 * k + 1) q = S := by
      intro k; simp [S, mathieuSpecB, Nat.not_even_bit1]
    have hmem : ∀ x : ℝ, x ∈ S ↔ deriv (mathieuWII x q) (π / 2) = 0 := by
      intro x; simp only [S, mathieuSpecB, Nat.not_even_one, ↓reduceIte, Set.mem_ofPred_eq]
    have hmemA : ∀ x : ℝ, x ∈ mathieuSpecA 1 q ↔ mathieuWI x q (π / 2) = 0 := by
      intro x; simp only [mathieuSpecA, Nat.not_even_one, ↓reduceIte, Set.mem_ofPred_eq]
    obtain ⟨x₀, hx₀⟩ := exists_lower_bound_of_encard_inter_Iio_eq_zero S (mathieuSpecB_exists 1 q 0)
    obtain ⟨y₀, hy₀⟩ := exists_lower_bound_of_encard_inter_Iio_eq_zero (mathieuSpecA 1 q)
        (mathieuSpecA_exists 1 q 0)
    have hfin : (S ∩ Iio a).Finite := by
      refine finite_inter_Iio_of_zeros (g := fun b => mathieuWI b q π + 1)
        ((differentiable_mathieuWI_mathieuWII_a _ _).1.add_const 1) (fun x hx => ?_) hx₀
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
    obtain ⟨k, hk⟩ := exists_eq_nthLeast ((hmem a).mpr hB') hfin
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
    obtain ⟨x₀, hx₀⟩ := exists_lower_bound_of_encard_inter_Iio_eq_zero S (mathieuSpecB_exists 2 q 0)
    have hfin : (S ∩ Iio a).Finite := by
      refine finite_inter_Iio_of_zeros (g := fun b => mathieuWII b q (π / 2))
        (differentiable_mathieuWI_mathieuWII_a _ _).2 (fun x hx => (hmem x).mp hx) hx₀
        (y := x₀ - 1) (fun h0 => ?_) a
      have := hx₀ _ ((hmem _).mpr h0); linarith
    obtain ⟨k, hk⟩ := exists_eq_nthLeast ((hmem a).mpr hB) hfin
    refine ⟨k, ?_⟩
    rw [hk]; simp only [mathieuB, show 2 * k + 2 ≠ 0 by omega, ↓reduceIte]
    rw [hS, show (2 * k + 2 - 1) / 2 = k by omega]
  · rintro ⟨n, rfl⟩
    obtain ⟨h1, h10, h11⟩ := mathieuWII_spec (mathieuB (2 * n + 2) q : ℂ) q
    exact ⟨_, h1, fun h => by
      have := congrArg (fun f => deriv f 0) h; simp [h11] at this, h10,
      mathieuWII_half_pi_mathieuB_even n q⟩

/-- The `(k+1)`-st smallest element exceeds the `k`-th. -/
private lemma nthLeast_lt_nthLeast_succ {S : Set ℝ} {k : ℕ} (hk : ∃ x ∈ S, (S ∩ Iio x).encard = k)
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
  exact nthLeast_lt_nthLeast_succ (mathieuSpecA_exists n q _) (mathieuSpecA_exists n q _)

/-- Monotone ordering within each spectrum of the `b_n` (DLMF §28.2(v)), `n ≥ 1`. -/
@[dlmf 28.2.v]
theorem mathieuB_lt_mathieuB_add_two {n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    mathieuB n q < mathieuB (n + 2) q := by
  have hS : mathieuSpecB (n + 2) q = mathieuSpecB n q := by
    simp [mathieuSpecB, Nat.even_add]
  simp only [mathieuB, hn, show n + 2 ≠ 0 by omega, ite_false, hS,
    show (n + 2 - 1) / 2 = (n - 1) / 2 + 1 by omega]
  exact nthLeast_lt_nthLeast_succ (mathieuSpecB_exists n q _) (mathieuSpecB_exists n q _)

/-- The eigenvalues `a_n(q)` are pairwise distinct. -/
lemma mathieuA_injective (q : ℝ) : Function.Injective fun n => mathieuA n q := by
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
lemma eq_of_mathieuB_eq {m n : ℕ} (hm0 : m ≠ 0) (hn0 : n ≠ 0) (q : ℝ)
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
theorem hasDerivAt_cos_const_mul (s z : ℂ) :
    HasDerivAt (fun z => Complex.cos (s * z)) (-Complex.sin (s * z) * s) z := by
  have := ((hasDerivAt_id' z).const_mul s).ccos
  convert this using 1; ring

/-- Derivative of `sin(sz)/s`. -/
private lemma hasDerivAt_sin_const_mul_div {s : ℂ} (hs0 : s ≠ 0) (z : ℂ) :
    HasDerivAt (fun z => Complex.sin (s * z) / s) (Complex.cos (s * z)) z := by
  have := (((hasDerivAt_id' z).const_mul s).csin).div_const s
  convert this using 1; field_simp

/-- `w_I(z; a, 0) = cos(sz)` for any `s` with `s² = a`. -/
theorem mathieuWI_q_zero {a s : ℂ} (hs : s ^ 2 = a) (z : ℂ) :
    mathieuWI a 0 z = Complex.cos (s * z) := by
  obtain ⟨h, h0, h1⟩ := mathieuWI_spec a 0
  have hdd : ∀ z, HasDerivAt (fun z => -Complex.sin (s * z) * s)
      (-(Complex.cos (s * z) * s) * s) z := fun z => by
    have := (((hasDerivAt_id' z).const_mul s).csin).neg.mul_const s
    convert this using 1; ring
  have hc : IsMathieuSolution a 0 (fun z => Complex.cos (s * z)) := by
    refine ⟨fun z => (hasDerivAt_cos_const_mul s z).differentiableAt, fun z => ?_⟩
    rw [show deriv (fun z => Complex.cos (s * z)) = fun z => -Complex.sin (s * z) * s from
      funext fun z => (hasDerivAt_cos_const_mul s z).deriv]
    convert hdd z using 1; rw [← hs]; ring
  have := h.eq_of_initial hc (z₀ := 0) (by simp [h0])
    (by rw [h1, (hasDerivAt_cos_const_mul s 0).deriv]; simp)
  exact congrFun this z

/-- `w_II(z; a, 0) = sin(sz)/s` for any `s ≠ 0` with `s² = a`. -/
theorem mathieuWII_q_zero {a s : ℂ} (hs : s ^ 2 = a) (hs0 : s ≠ 0) (z : ℂ) :
    mathieuWII a 0 z = Complex.sin (s * z) / s := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec a 0
  have hc : IsMathieuSolution a 0 (fun z => Complex.sin (s * z) / s) := by
    refine ⟨fun z => (hasDerivAt_sin_const_mul_div hs0 z).differentiableAt, fun z => ?_⟩
    rw [show deriv (fun z => Complex.sin (s * z) / s) = fun z => Complex.cos (s * z) from
      funext fun z => (hasDerivAt_sin_const_mul_div hs0 z).deriv]
    convert hasDerivAt_cos_const_mul s z using 1; rw [← hs]; field_simp; ring
  have := h.eq_of_initial hc (z₀ := 0) (by simp [h0])
    (by rw [h1, (hasDerivAt_sin_const_mul_div hs0 0).deriv]; simp)
  exact congrFun this z

/-- `w_II(z; 0, 0) = z`. -/
theorem mathieuWII_zero_zero (z : ℂ) : mathieuWII 0 0 z = z := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec 0 0
  have hc : IsMathieuSolution 0 0 (fun z => z) := by
    refine ⟨differentiable_id, fun z => ?_⟩
    rw [show deriv (fun z : ℂ => z) = fun _ => 1 from funext fun z => deriv_id z]
    simpa using hasDerivAt_const z (1 : ℂ)
  have := h.eq_of_initial hc (z₀ := 0) (by simp [h0]) (by rw [h1]; simp)
  exact congrFun this z

/-- `deriv w_I(·; s², 0) = -s sin(s ·)`. -/
theorem deriv_mathieuWI_q_zero {a s : ℂ} (hs : s ^ 2 = a) (z : ℂ) :
    deriv (mathieuWI a 0) z = -Complex.sin (s * z) * s := by
  rw [show mathieuWI a 0 = fun z => Complex.cos (s * z) from funext (mathieuWI_q_zero hs)]
  exact (hasDerivAt_cos_const_mul s z).deriv

/-- `deriv w_II(·; s², 0) = cos(s ·)`, `s ≠ 0`. -/
theorem deriv_mathieuWII_q_zero {a s : ℂ} (hs : s ^ 2 = a) (hs0 : s ≠ 0) (z : ℂ) :
    deriv (mathieuWII a 0) z = Complex.cos (s * z) := by
  rw [show mathieuWII a 0 = fun z => Complex.sin (s * z) / s from
    funext (mathieuWII_q_zero hs hs0)]
  exact (hasDerivAt_sin_const_mul_div hs0 z).deriv

/-- The `n`-th smallest element of the range of a strictly increasing sequence. -/
private lemma nthLeast_range_of_strictMono {f : ℕ → ℝ} (hf : StrictMono f) (n : ℕ) :
    nthLeast (range f) n = f n := by
  apply nthLeast_eq_of (Set.mem_range_self n)
  have e : range f ∩ Iio (f n) = f '' (Iio n) := by
    ext x; constructor
    · rintro ⟨⟨k, rfl⟩, hk⟩; exact Set.mem_image_of_mem f (hf.lt_iff_lt.mp hk)
    · rintro ⟨k, hk, rfl⟩; exact ⟨Set.mem_range_self k, hf (Set.mem_Iio.mp hk)⟩
  rw [e, hf.injective.injOn.encard_image]
  simp [Set.encard_eq_coe_toFinset_card]

/-- `s` with `s ⋅ π/2 = m π` is `2m`. -/
private lemma exists_eq_two_mul_of_sin_mul_pi_div_two_eq_zero {s : ℂ}
    (h : Complex.sin (s * (π / 2)) = 0) :
    ∃ m : ℤ, s = 2 * m := by
  obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp h
  refine ⟨m, ?_⟩
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_right_cancel₀ hπ; linear_combination 2 * hm

/-- `s` with `cos(s ⋅ π/2) = 0` is `2m + 1`. -/
private lemma exists_eq_two_mul_add_one_of_cos_mul_pi_div_two_eq_zero {s : ℂ}
    (h : Complex.cos (s * (π / 2)) = 0) :
    ∃ m : ℤ, s = 2 * m + 1 := by
  obtain ⟨m, hm⟩ := Complex.cos_eq_zero_iff.mp h
  refine ⟨m, ?_⟩
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  apply mul_right_cancel₀ hπ; linear_combination 2 * hm

/-- `|m|² = m²` in `ℂ`. -/
private lemma natCast_natAbs_sq_eq (m : ℤ) : ((m.natAbs : ℕ) : ℂ) ^ 2 = (m : ℂ) ^ 2 := by
  have := congrArg (fun t : ℤ => (t : ℂ)) (Int.natAbs_sq m)
  simpa only [Int.cast_pow, Int.cast_natCast] using this

/-- An odd integer squared is `(2j+1)²` for a natural `j`. -/
private lemma exists_two_mul_add_one_sq_eq_natCast (m : ℤ) : ∃ j : ℕ, ((2 * m + 1 : ℂ)) ^ 2 =
    ((2 * j + 1 : ℕ) : ℂ) ^ 2 := by
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
private lemma mathieuSpecA_even_q_zero (k : ℕ) :
    mathieuSpecA (2 * k) 0 = range fun j : ℕ => ((2 * j : ℕ) : ℝ) ^ 2 := by
  ext a
  simp only [mathieuSpecA, show Even (2 * k) from even_two_mul k, ↓reduceIte,
    Set.mem_ofPred_eq, mem_range, Complex.ofReal_zero]
  constructor
  · intro h
    set s := Complex.sqrt a
    have hs : s ^ 2 = a := DLMF.Elementary.Trigonometric.complexSqrt_sq _
    rw [deriv_mathieuWI_q_zero hs] at h
    obtain ⟨m, hm⟩ : ∃ m : ℤ, s = 2 * m := by
      rcases mul_eq_zero.mp h with h | h
      · exact exists_eq_two_mul_of_sin_mul_pi_div_two_eq_zero (by simpa using h)
      · exact ⟨0, by simp [h]⟩
    refine ⟨m.natAbs, ?_⟩
    have : ((a : ℝ) : ℂ) = ((((2 * m.natAbs : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hs, hm]; push_cast; rw [mul_pow, mul_pow, natCast_natAbs_sq_eq]
    exact_mod_cast this.symm
  · rintro ⟨j, rfl⟩
    have hs : ((2 * j : ℕ) : ℂ) ^ 2 = (((((2 * j : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [deriv_mathieuWI_q_zero hs]
    have : Complex.sin (((2 * j : ℕ) : ℂ) * (π / 2)) = 0 := by
      rw [Complex.sin_eq_zero_iff]; exact ⟨j, by push_cast; ring⟩
    rw [this]; simp

/-- The spectrum of the `a_{2k+1}` at `q = 0` is `{(2j+1)²}`. -/
private lemma mathieuSpecA_odd_q_zero (k : ℕ) :
    mathieuSpecA (2 * k + 1) 0 = range fun j : ℕ => ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
  ext a
  simp only [mathieuSpecA, Nat.not_even_bit1, ↓reduceIte,
    Set.mem_ofPred_eq, mem_range, Complex.ofReal_zero]
  constructor
  · intro h
    set s := Complex.sqrt a
    have hs : s ^ 2 = a := DLMF.Elementary.Trigonometric.complexSqrt_sq _
    rw [mathieuWI_q_zero hs] at h
    obtain ⟨m, hm⟩ := exists_eq_two_mul_add_one_of_cos_mul_pi_div_two_eq_zero h
    obtain ⟨j, hj⟩ := exists_two_mul_add_one_sq_eq_natCast m
    refine ⟨j, ?_⟩
    have : ((a : ℝ) : ℂ) = ((((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hs, hm, hj]; push_cast; ring
    exact_mod_cast this.symm
  · rintro ⟨j, rfl⟩
    have hs : ((2 * j + 1 : ℕ) : ℂ) ^ 2 = (((((2 * j + 1 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [mathieuWI_q_zero hs, Complex.cos_eq_zero_iff]
    exact ⟨j, by push_cast; ring⟩

/-- The spectrum of the `b_{2k+1}` at `q = 0` is `{(2j+1)²}`. -/
private lemma mathieuSpecB_odd_q_zero (k : ℕ) :
    mathieuSpecB (2 * k + 1) 0 = range fun j : ℕ => ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by
  ext a
  simp only [mathieuSpecB, Nat.not_even_bit1, ↓reduceIte,
    Set.mem_ofPred_eq, mem_range, Complex.ofReal_zero]
  constructor
  · intro h
    set s := Complex.sqrt a
    have hs : s ^ 2 = a := DLMF.Elementary.Trigonometric.complexSqrt_sq _
    rcases eq_or_ne s 0 with hs0 | hs0
    · exfalso
      have ha : (a : ℂ) = 0 := by rw [← hs, hs0]; ring
      rw [ha] at h
      rw [show mathieuWII 0 0 = fun z => z from funext mathieuWII_zero_zero] at h
      simp at h
    rw [deriv_mathieuWII_q_zero hs hs0] at h
    obtain ⟨m, hm⟩ := exists_eq_two_mul_add_one_of_cos_mul_pi_div_two_eq_zero h
    obtain ⟨j, hj⟩ := exists_two_mul_add_one_sq_eq_natCast m
    refine ⟨j, ?_⟩
    have : ((a : ℝ) : ℂ) = ((((2 * j + 1 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hs, hm, hj]; push_cast; ring
    exact_mod_cast this.symm
  · rintro ⟨j, rfl⟩
    have hs : ((2 * j + 1 : ℕ) : ℂ) ^ 2 = (((((2 * j + 1 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [deriv_mathieuWII_q_zero hs (Nat.cast_ne_zero.mpr (by omega)), Complex.cos_eq_zero_iff]
    exact ⟨j, by push_cast; ring⟩

/-- The spectrum of the `b_{2k+2}` at `q = 0` is `{(2j+2)²}`. -/
private lemma mathieuSpecB_even_q_zero (k : ℕ) :
    mathieuSpecB (2 * k + 2) 0 = range fun j : ℕ => ((2 * j + 2 : ℕ) : ℝ) ^ 2 := by
  ext a
  have he : Even (2 * k + 2) := ⟨k + 1, by ring⟩
  simp only [mathieuSpecB, he, ↓reduceIte, Set.mem_ofPred_eq, mem_range, Complex.ofReal_zero]
  constructor
  · intro h
    set s := Complex.sqrt a
    have hs : s ^ 2 = a := DLMF.Elementary.Trigonometric.complexSqrt_sq _
    rcases eq_or_ne s 0 with hs0 | hs0
    · exfalso
      have ha : (a : ℂ) = 0 := by rw [← hs, hs0]; ring
      rw [ha, mathieuWII_zero_zero] at h
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact hπ (by linear_combination 2 * h)
    rw [mathieuWII_q_zero hs hs0, div_eq_zero_iff, or_iff_left hs0] at h
    obtain ⟨m, hm⟩ := exists_eq_two_mul_of_sin_mul_pi_div_two_eq_zero h
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hs0 hm
    refine ⟨m.natAbs - 1, ?_⟩
    have hna : ((m.natAbs - 1 : ℕ) : ℂ) = (m.natAbs : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have : ((a : ℝ) : ℂ) = ((((2 * (m.natAbs - 1) + 2 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [← hs, hm]; push_cast; rw [hna]
      linear_combination (-4 : ℂ) * natCast_natAbs_sq_eq m
    exact_mod_cast this.symm
  · rintro ⟨j, rfl⟩
    have hs : ((2 * j + 2 : ℕ) : ℂ) ^ 2 = (((((2 * j + 2 : ℕ) : ℝ)) ^ 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [mathieuWII_q_zero hs (Nat.cast_ne_zero.mpr (by omega))]
    have : Complex.sin (((2 * j + 2 : ℕ) : ℂ) * (π / 2)) = 0 := by
      rw [Complex.sin_eq_zero_iff]; exact ⟨j + 1, by push_cast; ring⟩
    rw [this, zero_div]

/-- **DLMF 28.2.23**: `a_n(0) = n²`, `n = 0, 1, 2, …`. -/
@[dlmf 28.2.E23]
theorem mathieuA_zero (n : ℕ) : mathieuA n 0 = (n : ℝ) ^ 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [mathieuA, mathieuSpecA_even_q_zero, show 2 * k / 2 = k by omega,
      nthLeast_range_of_strictMono (by intro i j h; simp only; gcongr)]
  · rw [mathieuA, mathieuSpecA_odd_q_zero, show (2 * k + 1) / 2 = k by omega,
      nthLeast_range_of_strictMono (by intro i j h; simp only; gcongr)]

/-- **DLMF 28.2.24**: `b_n(0) = n²`, `n = 1, 2, 3, …`. -/
@[dlmf 28.2.E24]
theorem mathieuB_zero {n : ℕ} (hn : n ≠ 0) : mathieuB n 0 = (n : ℝ) ^ 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [mathieuB, hn, ↓reduceIte]
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, mathieuSpecB_even_q_zero,
      show (2 * j + 2 - 1) / 2 = j by omega,
      nthLeast_range_of_strictMono (by intro i j h; simp only; gcongr)]
  · simp only [mathieuB, hn, ↓reduceIte]
    rw [mathieuSpecB_odd_q_zero, show (2 * k + 1 - 1) / 2 = k by omega,
      nthLeast_range_of_strictMono (by intro i j h; simp only; gcongr)]

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
    simp [mathieuSpecA, deriv_mathieuWI_half_pi_neg_q]
  simp only [mathieuA, hS]

/-- **DLMF 28.2.27**: `a_{2n+1}(-q) = b_{2n+1}(q)`. -/
@[dlmf 28.2.E27]
theorem mathieuA_odd_neg (n : ℕ) (q : ℝ) :
    mathieuA (2 * n + 1) (-q) = mathieuB (2 * n + 1) q := by
  have hS : mathieuSpecA (2 * n + 1) (-q) = mathieuSpecB (2 * n + 1) q := by
    ext a
    simp [mathieuSpecA, mathieuSpecB, Nat.not_even_bit1, mathieuWI_half_pi_neg_q]
  simp only [mathieuA, mathieuB, hS, show 2 * n + 1 ≠ 0 by omega, ite_false,
    show (2 * n + 1) / 2 = (2 * n + 1 - 1) / 2 by omega]

/-- **DLMF 28.2.28**: `b_{2n+2}(-q) = b_{2n+2}(q)`. -/
@[dlmf 28.2.E28]
theorem mathieuB_even_neg (n : ℕ) (q : ℝ) :
    mathieuB (2 * n + 2) (-q) = mathieuB (2 * n + 2) q := by
  have hS : mathieuSpecB (2 * n + 2) (-q) = mathieuSpecB (2 * n + 2) q := by
    ext a
    have he : Even (2 * n + 2) := ⟨n + 1, by ring⟩
    simp [mathieuSpecB, he, mathieuWII_half_pi_neg_q]
  simp only [mathieuB, hS]

end DLMF.Mathieu
end
