/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Data.Set.Card
public import DLMFMathlib.Analysis.ODE.PowerSeriesUniqueness
public import DLMFMathlib.Analysis.ODE.SturmCount

/-!
# Eigenvalues of regular Sturm–Liouville boundary problems on `[0, L]`

Let `y(x, λ)` solve `y'' = (Q(x) - λ) y` on `ℝ` with fixed initial data at `0`, either
`(y, y')(0) = (1, 0)` or `(0, 1)`, where `Q` is bounded on `[0, L]`. The boundary function
`g(λ) = y(L, λ)` or `g(λ) = y'(L, λ)`

* does not vanish for `λ < -M`, where `|Q| ≤ M` on `[0, L]` (`ODE.p2s_endpoint_ne_zero`:
  `y y'` is increasing on `[0, L]`);
* takes both signs for arbitrarily large `λ` (`ODE.p2s_signs_I_val` and its three
  companions), from the energy estimate `ODE.p2s_energy_le` comparing `y` with the solution
  `α cos kx + (β / k) sin kx` of `y'' = -k² y` (Grönwall);

so, when `g` is the restriction of an entire function, its zeros form an increasing sequence
tending to `+∞` (`ODE.p2s_exists_encard_zeros`): for every `k` there is a zero with exactly `k`
smaller zeros. This is the existence part of the classical theory of the eigenvalues of
regular Sturm–Liouville problems with separated boundary conditions, used for the Mathieu
eigenvalues `a_n(q)`, `b_n(q)` (DLMF §28.2(v)).

We also record that a solution of a real linear equation with real data is real
(`ODE.p2s_conj_eq_of_linear_ode`).
-/

@[expose] public section

open Set Filter Topology Real

namespace ODE

/-! ### Sets of reals enumerated in increasing order -/

/-- A set of reals all of whose initial segments `S ∩ (-∞, x)` are finite has a least element
in each of its nonempty subsets. -/
theorem p2s_exists_least {S T : Set ℝ} (hfin : ∀ x, (S ∩ Iio x).Finite) (hTS : T ⊆ S)
    (hT : T.Nonempty) : ∃ m ∈ T, ∀ t ∈ T, m ≤ t := by
  obtain ⟨z, hz⟩ := hT
  have hF : (T ∩ Iic z).Finite := by
    refine ((hfin z).union (finite_singleton z)).subset fun t ht => ?_
    rcases eq_or_lt_of_le ht.2 with h | h
    · exact Or.inr h
    · exact Or.inl ⟨hTS ht.1, h⟩
  obtain ⟨m, hm, hmin⟩ := Set.exists_min_image (T ∩ Iic z) id hF ⟨z, hz, le_rfl⟩
  refine ⟨m, hm.1, fun t ht => ?_⟩
  rcases le_total t z with h | h
  · exact hmin t ⟨ht, h⟩
  · exact hm.2.trans h

/-- **Enumeration of a discrete set bounded below.** If `S ⊆ ℝ` is infinite and all its initial
segments `S ∩ (-∞, x)` are finite, then for every `k` some element of `S` has exactly `k`
smaller elements in `S`. -/
theorem p2s_exists_encard_eq {S : Set ℝ} (hinf : S.Infinite) (hfin : ∀ x, (S ∩ Iio x).Finite)
    (k : ℕ) : ∃ x ∈ S, (S ∩ Iio x).encard = k := by
  induction k with
  | zero =>
    obtain ⟨m, hm, hmin⟩ := p2s_exists_least hfin subset_rfl hinf.nonempty
    refine ⟨m, hm, ?_⟩
    rw [Nat.cast_zero, Set.encard_eq_zero, eq_empty_iff_forall_notMem]
    exact fun t ht => absurd (hmin t ht.1) (not_le.mpr ht.2)
  | succ k ih =>
    obtain ⟨x, hx, hxk⟩ := ih
    have hT : (S ∩ Ioi x).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      refine hinf (((hfin x).union (finite_singleton x)).subset fun t ht => ?_)
      rcases lt_trichotomy t x with h' | h' | h'
      · exact Or.inl ⟨ht, h'⟩
      · exact Or.inr h'
      · exact absurd (show t ∈ S ∩ Ioi x from ⟨ht, h'⟩) (h ▸ notMem_empty t)
    obtain ⟨m, hm, hmin⟩ := p2s_exists_least hfin inter_subset_left hT
    refine ⟨m, hm.1, ?_⟩
    have hset : S ∩ Iio m = insert x (S ∩ Iio x) := by
      ext t
      simp only [mem_inter_iff, mem_Iio, mem_insert_iff]
      constructor
      · rintro ⟨ht, htm⟩
        rcases lt_trichotomy t x with h' | h' | h'
        · exact Or.inr ⟨ht, h'⟩
        · exact Or.inl h'
        · exact absurd (hmin t ⟨ht, h'⟩) (not_le.mpr htm)
      · rintro (rfl | ⟨ht, htx⟩)
        · exact ⟨hx, hm.2⟩
        · exact ⟨ht, htx.trans hm.2⟩
    rw [hset, Set.encard_insert_of_notMem (fun h : x ∈ S ∩ Iio x => lt_irrefl x h.2), hxk]
    push_cast; rfl

/-! ### Zeros of real restrictions of entire functions -/

/-- The restriction to `ℝ` of the real part of an entire function is real analytic. -/
theorem p2s_analyticAt_re {G : ℂ → ℂ} (hG : Differentiable ℂ G) (x : ℝ) :
    AnalyticAt ℝ (fun t : ℝ => (G t).re) x := by
  have h1 : AnalyticAt ℝ G (x : ℂ) := (hG.analyticAt (x : ℂ)).restrictScalars
  have h2 : AnalyticAt ℝ (fun t : ℝ => (t : ℂ)) x := Complex.ofRealCLM.analyticAt x
  exact Complex.reCLM.analyticAt _ |>.comp (h1.comp h2)

/-- The zeros in a compact interval of a real analytic function on `ℝ` that does not vanish
identically are finite in number. -/
theorem p2s_finite_zeros_Icc {g : ℝ → ℝ} (hg : ∀ x, AnalyticAt ℝ g x) {x₀ : ℝ} (hx₀ : g x₀ ≠ 0)
    (a b : ℝ) : {x | x ∈ Icc a b ∧ g x = 0}.Finite := by
  have hc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  have hK : IsCompact {x | x ∈ Icc a b ∧ g x = 0} :=
    isCompact_Icc.of_isClosed_subset (isClosed_Icc.inter (isClosed_eq hc continuous_const))
      fun x hx => hx.1
  by_contra hinf
  obtain ⟨z, -, hne⟩ := exists_nhds_ne_inf_principal_neBot hK hinf
  have hfr : ∃ᶠ x in 𝓝[≠] z, g x = 0 := by
    rw [Filter.frequently_iff_neBot]
    exact hne.mono (inf_le_inf_left _ (principal_mono.mpr fun x hx => hx.2))
  have := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero (U := univ)
    (fun x _ => hg x) isPreconnected_univ (mem_univ z) hfr (mem_univ x₀)
  exact hx₀ this

/-- **Enumeration of the zeros.** Let `g : ℝ → ℝ` be the restriction of an entire function, with
no zeros below some `c`, and taking both signs for arbitrarily large arguments. Then for every
`k` some zero of `g` has exactly `k` smaller zeros. -/
theorem p2s_exists_encard_zeros {g : ℝ → ℝ} {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hGg : ∀ x : ℝ, G x = g x) (hlow : ∃ c, ∀ x < c, g x ≠ 0) (hpos : ∀ N, ∃ x > N, 0 < g x)
    (hneg : ∀ N, ∃ x > N, g x < 0) (k : ℕ) :
    ∃ x ∈ {x | g x = 0}, ({x | g x = 0} ∩ Iio x).encard = k := by
  have hgre : g = fun t : ℝ => (G t).re := funext fun t => by rw [hGg]; simp
  have hg : ∀ x, AnalyticAt ℝ g x := fun x => hgre ▸ p2s_analyticAt_re hG x
  have hc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  obtain ⟨c, hcg⟩ := hlow
  refine p2s_exists_encard_eq ?_ (fun x => ?_) k
  · exact (sturmCount_infinite_zeros_atTop (c := c) hc.continuousOn hpos hneg).mono
      (by intro x hx; exact hx.2)
  · refine (p2s_finite_zeros_Icc hg (hcg (c - 1) (by linarith)) c x).subset ?_
    rintro t ⟨ht0, htx⟩
    refine ⟨⟨?_, htx.le⟩, ht0⟩
    by_contra h
    exact hcg t (not_le.mp h) ht0

/-! ### The energy estimate for large `λ` -/

/-- **Energy estimate.** Let `y'' = (Q - k²) y` with `|Q| ≤ M` on `[0, L]`, `k ≥ 1`, and
`(y, y')(0) = (α, β)`. Compare `y` with `c(x) = α cos kx + (β / k) sin kx`, the solution of
`c'' = -k² c` with the same data. The energy `E = (y' - c')² + k² (y - c)²` satisfies
`E' = 2 (y' - c') Q y ≤ 3 M E + 2 M A²` with `A = |α| + |β| / k`, so by Grönwall
`E(x) ≤ (2 A² / 3) (e^{3 M x} - 1)` on `[0, L]`. -/
theorem p2s_energy_le {Q y y' : ℝ → ℝ} {M L k α β : ℝ} (hM : 0 < M) (hk : 1 ≤ k)
    (hQ : ∀ x ∈ Icc 0 L, |Q x| ≤ M) (hy : ∀ x, HasDerivAt y (y' x) x)
    (hy' : ∀ x, HasDerivAt y' ((Q x - k ^ 2) * y x) x) (h0 : y 0 = α) (h1 : y' 0 = β)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    (y' x - (-(α * k * sin (k * x)) + β * cos (k * x))) ^ 2 +
        k ^ 2 * (y x - (α * cos (k * x) + β / k * sin (k * x))) ^ 2 ≤
      2 * (|α| + |β| / k) ^ 2 / 3 * (exp (3 * M * x) - 1) := by
  have hk0 : 0 < k := by linarith
  set A := |α| + |β| / k with hA
  have hA0 : 0 ≤ A := by positivity
  set c : ℝ → ℝ := fun x => α * cos (k * x) + β / k * sin (k * x) with hc
  set c' : ℝ → ℝ := fun x => -(α * k * sin (k * x)) + β * cos (k * x) with hc'
  have hdc : ∀ x, HasDerivAt c (c' x) x := by
    intro x
    have h1 := ((hasDerivAt_id x).const_mul k).cos
    have h2 := ((hasDerivAt_id x).const_mul k).sin
    refine ((h1.const_mul α).add (h2.const_mul (β / k))).congr_deriv ?_
    simp only [hc', id, mul_one]
    field_simp
  have hdc' : ∀ x, HasDerivAt c' (-(k ^ 2) * c x) x := by
    intro x
    have h1 := ((hasDerivAt_id x).const_mul k).cos
    have h2 := ((hasDerivAt_id x).const_mul k).sin
    refine ((h2.const_mul (α * k)).neg.add (h1.const_mul β)).congr_deriv ?_
    simp only [hc, id, mul_one]
    field_simp
    ring
  have hcA : ∀ x, |c x| ≤ A := by
    intro x
    calc |c x| ≤ |α * cos (k * x)| + |β / k * sin (k * x)| := abs_add_le _ _
      _ ≤ |α| * 1 + |β / k| * 1 := by
          rw [abs_mul, abs_mul]
          gcongr
          · exact abs_cos_le_one _
          · exact abs_sin_le_one _
      _ = A := by rw [abs_div, abs_of_pos hk0]; ring
  set E : ℝ → ℝ := fun x => (y' x - c' x) ^ 2 + k ^ 2 * (y x - c x) ^ 2 with hE
  set E' : ℝ → ℝ := fun x => 2 * (y' x - c' x) * (Q x * y x) with hE'
  have hdE : ∀ x, HasDerivAt E (E' x) x := by
    intro x
    have h1 := ((hy' x).sub (hdc' x)).pow 2
    have h2 := (((hy x).sub (hdc x)).pow 2).const_mul (k ^ 2)
    convert h1.add h2 using 1
    simp only [hE', Nat.cast_ofNat, Pi.sub_apply]
    ring
  have hbound : ∀ x ∈ Ico 0 L, E' x ≤ 3 * M * E x + 2 * M * A ^ 2 := by
    intro x hx
    set a := y' x - c' x
    set b := y x - c x
    have hyx : y x = b + c x := by simp [b]
    have hQx := hQ x (Ico_subset_Icc_self hx)
    have e1 : 2 * a * (Q x * y x) ≤ 2 * |a| * (M * |y x|) := by
      have : 2 * a * (Q x * y x) ≤ |2 * a * (Q x * y x)| := le_abs_self _
      rw [abs_mul, abs_mul, abs_mul, abs_two] at this
      have : |Q x| * |y x| ≤ M * |y x| := mul_le_mul_of_nonneg_right hQx (abs_nonneg _)
      nlinarith [abs_nonneg a]
    have e2 : 2 * |a| * (M * |y x|) ≤ M * (a ^ 2 + y x ^ 2) := by
      have : 0 ≤ (|a| - |y x|) ^ 2 := sq_nonneg _
      have ha : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
      have hy2 : y x ^ 2 = |y x| ^ 2 := (sq_abs _).symm
      nlinarith
    have e3 : y x ^ 2 ≤ 2 * b ^ 2 + 2 * c x ^ 2 := by
      rw [hyx]; nlinarith [sq_nonneg (b - c x)]
    have e4 : c x ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs (c x)]; exact pow_le_pow_left₀ (abs_nonneg _) (hcA x) 2
    have e5 : b ^ 2 ≤ k ^ 2 * b ^ 2 := by
      have : 1 ≤ k ^ 2 := by nlinarith
      nlinarith [sq_nonneg b]
    show 2 * a * (Q x * y x) ≤ 3 * M * (a ^ 2 + k ^ 2 * b ^ 2) + 2 * M * A ^ 2
    nlinarith [sq_nonneg a]
  have hG := le_gronwallBound_of_liminf_deriv_right_le (f := E) (f' := E') (δ := 0)
    (K := 3 * M) (ε := 2 * M * A ^ 2) (a := 0) (b := L)
    (fun x _ => (hdE x).continuousAt.continuousWithinAt)
    (fun x _ r hr => (hdE x).hasDerivWithinAt.liminf_right_slope_le hr)
    (by simp [hE, h0, h1, hc, hc']) hbound x hx
  rw [gronwallBound_of_K_ne_0 (by positivity), sub_zero] at hG
  convert hG using 1
  field_simp
  ring

/-! ### No eigenvalues below `-M` -/

/-- **No zeros at the end for very negative `λ`.** Let `y'' = (Q - λ) y` with `|Q| ≤ M` on
`[0, L]` and `λ < -M`, with `y(0) y'(0) ≥ 0` and `(y, y')(0) ≠ 0`. Then `y(L) ≠ 0` and
`y'(L) ≠ 0`: `(y y')' = y'² + (Q - λ) y² ≥ 0`, so `y y'` increases on `[0, L]`, and it cannot
vanish at `L` without `y` and `y'` vanishing on `(0, L)`. -/
theorem p2s_endpoint_ne_zero {Q y y' : ℝ → ℝ} {M L μ : ℝ} (hL : 0 < L)
    (hQ : ∀ x ∈ Icc 0 L, |Q x| ≤ M) (hμ : μ < -M) (hy : ∀ x, HasDerivAt y (y' x) x)
    (hy' : ∀ x, HasDerivAt y' ((Q x - μ) * y x) x) (h0 : 0 ≤ y 0 * y' 0)
    (hne : y 0 ≠ 0 ∨ y' 0 ≠ 0) : y L ≠ 0 ∧ y' L ≠ 0 := by
  have hpos : ∀ x ∈ Icc 0 L, 0 < Q x - μ := fun x hx => by
    linarith [(abs_le.mp (hQ x hx)).1]
  have hu : ∀ x, HasDerivAt (fun x => y x * y' x)
      (y' x * y' x + y x * ((Q x - μ) * y x)) x := fun x => (hy x).mul (hy' x)
  have hmono : MonotoneOn (fun x => y x * y' x) (Icc 0 L) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 L)
      (fun x _ => (hu x).continuousAt.continuousWithinAt) (fun x _ => (hu x).hasDerivWithinAt)
      fun x hx => ?_
    have := hpos x (interior_subset hx)
    nlinarith [mul_self_nonneg (y' x), mul_nonneg this.le (mul_self_nonneg (y x))]
  by_contra hcon
  have huL : y L * y' L = 0 := by
    rcases not_and_or.mp hcon with h | h
    · rw [not_not.mp h, zero_mul]
    · rw [not_not.mp h, mul_zero]
  have hmem0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  have hmemL : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
  have hu0 : ∀ x ∈ Icc 0 L, y x * y' x = 0 := fun x hx => le_antisymm
    ((hmono hx hmemL hx.2).trans huL.le) (h0.trans (hmono hmem0 hx hx.1))
  have hz : ∀ x ∈ Ioo 0 L, y x = 0 ∧ y' x = 0 := by
    intro x hx
    have hev : (fun x => y x * y' x) =ᶠ[𝓝 x] fun _ => 0 :=
      Filter.eventually_of_mem (Ioo_mem_nhds hx.1 hx.2) fun t ht => hu0 t (Ioo_subset_Icc_self ht)
    have hd := (hu x).unique ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev)
    have hp := hpos x (Ioo_subset_Icc_self hx)
    have h2 : (Q x - μ) * (y x * y x) = 0 := by
      nlinarith [mul_self_nonneg (y' x), mul_nonneg hp.le (mul_self_nonneg (y x))]
    have h3 : y x = 0 := mul_self_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hp.ne')
    refine ⟨h3, mul_self_eq_zero.mp ?_⟩
    rw [h3] at hd; linarith
  have hcl : ∀ {f : ℝ → ℝ}, Continuous f → (∀ x ∈ Ioo 0 L, f x = 0) → f 0 = 0 := by
    intro f hf hf0
    have : closure (Ioo (0 : ℝ) L) ⊆ {x | f x = 0} :=
      (isClosed_eq hf continuous_const).closure_subset_iff.mpr hf0
    rw [closure_Ioo hL.ne] at this
    exact this hmem0
  have hyc : Continuous y := continuous_iff_continuousAt.mpr fun x => (hy x).continuousAt
  have hyc' : Continuous y' := continuous_iff_continuousAt.mpr fun x => (hy' x).continuousAt
  rcases hne with h | h
  · exact h (hcl hyc fun x hx => (hz x hx).1)
  · exact h (hcl hyc' fun x hx => (hz x hx).2)

/-! ### Sign changes for large `λ` -/

/-- If `(-1)^j g(t_j) > 0` for all large `j` and `t_j → ∞`, then `g` takes positive and negative
values for arbitrarily large arguments. -/
theorem p2s_pos_neg_of_alternating {g : ℝ → ℝ} {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) {J : ℕ}
    (h : ∀ j ≥ J, 0 < (-1) ^ j * g (t j)) :
    (∀ N, ∃ x > N, 0 < g x) ∧ (∀ N, ∃ x > N, g x < 0) := by
  have key : ∀ N, ∃ j, J ≤ j ∧ Even j ∧ N < t j ∧ N < t (j + 1) := by
    intro N
    obtain ⟨J', hJ'⟩ := eventually_atTop.mp (ht.eventually_gt_atTop N)
    exact ⟨2 * (J + J'), by omega, even_two_mul _, hJ' _ (by omega), hJ' _ (by omega)⟩
  refine ⟨fun N => ?_, fun N => ?_⟩
  · obtain ⟨j, hj, he, hN, -⟩ := key N
    have := h j hj
    rw [he.neg_one_pow, one_mul] at this
    exact ⟨t j, hN, this⟩
  · obtain ⟨j, hj, he, -, hN⟩ := key N
    have := h (j + 1) (by omega)
    rw [(he.add_one).neg_one_pow] at this
    exact ⟨t (j + 1), hN, by linarith⟩

/-- `u v > 0` when `(u - v)² < v²`. -/
theorem p2s_mul_pos_of_sq_lt {u v : ℝ} (h : (u - v) ^ 2 < v ^ 2) : 0 < v * u := by
  nlinarith [sq_nonneg u]

/-- The frequencies `k_j = (j π + φ) / L` tend to `+∞`, and so do `k_j²`; eventually
`k_j ≥ 1` and `k_j² > B`. -/
theorem p2s_freq_eventually {L φ : ℝ} (hL : 0 < L) (B : ℝ) :
    Tendsto (fun j : ℕ => ((j * π + φ) / L) ^ 2) atTop atTop ∧
      ∃ J : ℕ, ∀ j ≥ J, 1 ≤ (j * π + φ) / L ∧ B < ((j * π + φ) / L) ^ 2 := by
  have h1 : Tendsto (fun j : ℕ => (j * π + φ) / L) atTop atTop := by
    have : Tendsto (fun j : ℕ => (j : ℝ) * (π / L) + φ / L) atTop atTop :=
      tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.atTop_mul_const (div_pos pi_pos hL))
    refine this.congr fun j => ?_
    field_simp
  refine ⟨(tendsto_pow_atTop two_ne_zero).comp h1, ?_⟩
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (h1.eventually_ge_atTop (max 1 (|B| + 1)))
  refine ⟨J, fun j hj => ?_⟩
  have h := hJ j hj
  have ha := le_max_left 1 (|B| + 1)
  have hb := le_max_right 1 (|B| + 1)
  have hB := le_abs_self B
  exact ⟨ha.trans h, by nlinarith⟩

/-- `k_j L = j π + φ` for `k_j = (j π + φ) / L`. -/
theorem p2s_freq_mul {L φ : ℝ} (hL : 0 < L) (j : ℕ) : (j * π + φ) / L * L = j * π + φ := by
  field_simp

variable {Q : ℝ → ℝ} {Y Y' : ℝ → ℝ → ℝ} {M L : ℝ}

/-- **Sign changes of `y(L, λ)`** for `(y, y')(0) = (1, 0)`: at `λ = k_j²`, `k_j = jπ / L`,
the sign of `y(L, λ)` is `(-1)^j` for large `j`. -/
theorem p2s_signs_I_val (hM : 0 < M) (hL : 0 < L) (hQ : ∀ x ∈ Icc 0 L, |Q x| ≤ M)
    (hY : ∀ μ x, HasDerivAt (Y μ) (Y' μ x) x)
    (hY' : ∀ μ x, HasDerivAt (Y' μ) ((Q x - μ) * Y μ x) x) (h0 : ∀ μ, Y μ 0 = 1)
    (h1 : ∀ μ, Y' μ 0 = 0) :
    (∀ N, ∃ μ > N, 0 < Y μ L) ∧ (∀ N, ∃ μ > N, Y μ L < 0) := by
  obtain ⟨ht, J, hJ⟩ := p2s_freq_eventually (φ := 0) hL
    (2 * (|1| + |0| / 1) ^ 2 / 3 * (exp (3 * M * L) - 1))
  refine p2s_pos_neg_of_alternating (g := fun μ => Y μ L) ht (J := J) fun j hj => ?_
  obtain ⟨hk1, hkB⟩ := hJ j hj
  set k := (j * π + 0) / L
  have hE := p2s_energy_le hM hk1 hQ (hY (k ^ 2)) (hY' (k ^ 2)) (h0 _) (h1 _)
    (x := L) ⟨hL.le, le_rfl⟩
  rw [p2s_freq_mul hL, add_zero, cos_nat_mul_pi, sin_nat_mul_pi] at hE
  simp only [abs_one, abs_zero, zero_div, add_zero, zero_mul, mul_zero, one_mul] at hE
  have hs : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  refine p2s_mul_pos_of_sq_lt ?_
  rw [hs]
  have hk2 : 0 < k ^ 2 := by positivity
  by_contra hcon
  push Not at hcon
  nlinarith [sq_nonneg (Y' (k ^ 2) L), mul_le_mul_of_nonneg_left hcon hk2.le]

/-- **Sign changes of `y'(L, λ)`** for `(y, y')(0) = (1, 0)`: at `λ = k_j²`,
`k_j = (jπ + π/2) / L`, the sign of `y'(L, λ)` is `-(-1)^j` for large `j`. -/
theorem p2s_signs_I_der (hM : 0 < M) (hL : 0 < L) (hQ : ∀ x ∈ Icc 0 L, |Q x| ≤ M)
    (hY : ∀ μ x, HasDerivAt (Y μ) (Y' μ x) x)
    (hY' : ∀ μ x, HasDerivAt (Y' μ) ((Q x - μ) * Y μ x) x) (h0 : ∀ μ, Y μ 0 = 1)
    (h1 : ∀ μ, Y' μ 0 = 0) :
    (∀ N, ∃ μ > N, 0 < Y' μ L) ∧ (∀ N, ∃ μ > N, Y' μ L < 0) := by
  obtain ⟨ht, J, hJ⟩ := p2s_freq_eventually (φ := π / 2) hL
    (2 * (|1| + |0| / 1) ^ 2 / 3 * (exp (3 * M * L) - 1))
  have := p2s_pos_neg_of_alternating (g := fun μ => -Y' μ L) ht (J := J) fun j hj => ?_
  · exact ⟨fun N => let ⟨μ, h, h'⟩ := this.2 N; ⟨μ, h, by linarith⟩,
      fun N => let ⟨μ, h, h'⟩ := this.1 N; ⟨μ, h, by linarith⟩⟩
  obtain ⟨hk1, hkB⟩ := hJ j hj
  set k := (j * π + π / 2) / L
  have hE := p2s_energy_le hM hk1 hQ (hY (k ^ 2)) (hY' (k ^ 2)) (h0 _) (h1 _)
    (x := L) ⟨hL.le, le_rfl⟩
  rw [p2s_freq_mul hL, sin_add_pi_div_two, cos_nat_mul_pi] at hE
  simp only [abs_one, abs_zero, zero_div, add_zero, zero_mul, one_mul] at hE
  have hs : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hk0 : 0 < k := by linarith
  have key := p2s_mul_pos_of_sq_lt (u := Y' (k ^ 2) L) (v := -(k * (-1) ^ j)) (by
    rw [neg_sq, mul_pow, hs, mul_one]
    simp only [abs_one, abs_zero, zero_div, add_zero] at hkB
    nlinarith [mul_nonneg (sq_nonneg k) (sq_nonneg (Y (k ^ 2) L - cos (j * π + π / 2)))])
  have : 0 < k * ((-1) ^ j * -Y' (k ^ 2) L) := by linarith
  exact pos_of_mul_pos_right this hk0.le

/-- **Sign changes of `y(L, λ)`** for `(y, y')(0) = (0, 1)`: at `λ = k_j²`,
`k_j = (jπ + π/2) / L`, the sign of `y(L, λ)` is `(-1)^j` for large `j`. -/
theorem p2s_signs_II_val (hM : 0 < M) (hL : 0 < L) (hQ : ∀ x ∈ Icc 0 L, |Q x| ≤ M)
    (hY : ∀ μ x, HasDerivAt (Y μ) (Y' μ x) x)
    (hY' : ∀ μ x, HasDerivAt (Y' μ) ((Q x - μ) * Y μ x) x) (h0 : ∀ μ, Y μ 0 = 0)
    (h1 : ∀ μ, Y' μ 0 = 1) :
    (∀ N, ∃ μ > N, 0 < Y μ L) ∧ (∀ N, ∃ μ > N, Y μ L < 0) := by
  obtain ⟨ht, J, hJ⟩ := p2s_freq_eventually (φ := π / 2) hL
    (2 * (|1| + |0| / 1) ^ 2 / 3 * (exp (3 * M * L) - 1))
  refine p2s_pos_neg_of_alternating (g := fun μ => Y μ L) ht (J := J) fun j hj => ?_
  obtain ⟨hk1, hkB⟩ := hJ j hj
  set k := (j * π + π / 2) / L
  have hE := p2s_energy_le hM hk1 hQ (hY (k ^ 2)) (hY' (k ^ 2)) (h0 _) (h1 _)
    (x := L) ⟨hL.le, le_rfl⟩
  rw [p2s_freq_mul hL, sin_add_pi_div_two, cos_nat_mul_pi] at hE
  simp only [abs_one, abs_zero, zero_div, add_zero, zero_mul, zero_add, one_mul,
    neg_zero] at hE hkB
  have hk0 : 0 < k := by linarith
  have hk2 : 0 < k ^ 2 := by positivity
  have hs : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hR : 2 * (1 / k) ^ 2 / 3 * (exp (3 * M * L) - 1) =
      2 * 1 ^ 2 / 3 * (exp (3 * M * L) - 1) / k ^ 2 := by field_simp
  have hlt := (div_lt_one hk2).mpr hkB
  rw [hR] at hE
  have hX : k ^ 2 * (Y (k ^ 2) L - 1 / k * (-1) ^ j) ^ 2 < 1 := by
    linarith [sq_nonneg (Y' (k ^ 2) L - cos (j * π + π / 2))]
  have hv : (1 / k * (-1) ^ j) ^ 2 = 1 / k ^ 2 := by rw [mul_pow, hs]; field_simp
  have key := p2s_mul_pos_of_sq_lt (u := Y (k ^ 2) L) (v := 1 / k * (-1) ^ j) (by
    rw [hv, lt_div_iff₀ hk2]; linarith)
  rw [mul_assoc] at key
  exact pos_of_mul_pos_right key (by positivity)

/-- **Sign changes of `y'(L, λ)`** for `(y, y')(0) = (0, 1)`: at `λ = k_j²`, `k_j = jπ / L`,
the sign of `y'(L, λ)` is `(-1)^j` for large `j`. -/
theorem p2s_signs_II_der (hM : 0 < M) (hL : 0 < L) (hQ : ∀ x ∈ Icc 0 L, |Q x| ≤ M)
    (hY : ∀ μ x, HasDerivAt (Y μ) (Y' μ x) x)
    (hY' : ∀ μ x, HasDerivAt (Y' μ) ((Q x - μ) * Y μ x) x) (h0 : ∀ μ, Y μ 0 = 0)
    (h1 : ∀ μ, Y' μ 0 = 1) :
    (∀ N, ∃ μ > N, 0 < Y' μ L) ∧ (∀ N, ∃ μ > N, Y' μ L < 0) := by
  obtain ⟨ht, J, hJ⟩ := p2s_freq_eventually (φ := 0) hL
    (2 * (|1| + |0| / 1) ^ 2 / 3 * (exp (3 * M * L) - 1))
  refine p2s_pos_neg_of_alternating (g := fun μ => Y' μ L) ht (J := J) fun j hj => ?_
  obtain ⟨hk1, hkB⟩ := hJ j hj
  set k := (j * π + 0) / L
  have hE := p2s_energy_le hM hk1 hQ (hY (k ^ 2)) (hY' (k ^ 2)) (h0 _) (h1 _)
    (x := L) ⟨hL.le, le_rfl⟩
  rw [p2s_freq_mul hL, add_zero, cos_nat_mul_pi, sin_nat_mul_pi] at hE
  simp only [abs_one, abs_zero, zero_div, add_zero, zero_mul, zero_add, one_mul,
    neg_zero, mul_zero, sub_zero] at hE hkB
  have hk0 : 0 < k := by linarith
  have hk2 : 0 < k ^ 2 := by positivity
  have hs : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hR : 2 * (1 / k) ^ 2 / 3 * (exp (3 * M * L) - 1) =
      2 * 1 ^ 2 / 3 * (exp (3 * M * L) - 1) / k ^ 2 := by field_simp
  have hlt := (div_lt_one hk2).mpr hkB
  rw [hR] at hE
  refine p2s_mul_pos_of_sq_lt ?_
  rw [hs]
  nlinarith [mul_nonneg hk2.le (sq_nonneg (Y (k ^ 2) L))]

/-! ### Real solutions -/

/-- **Solutions of real equations with real data are real.** If `f'' = P f` on `ℝ` with `P`
real and continuous, and `f(t₀)`, `f'(t₀)` are real, then `f` and `f'` are real on `ℝ`. -/
theorem p2s_conj_eq_of_linear_ode {P : ℝ → ℝ} (hP : Continuous P) {f f' : ℝ → ℂ}
    (hf : ∀ t, HasDerivAt f (f' t) t ∧ HasDerivAt f' ((P t : ℂ) * f t) t) {t₀ : ℝ}
    (h0 : (starRingEnd ℂ) (f t₀) = f t₀) (h1 : (starRingEnd ℂ) (f' t₀) = f' t₀) (t : ℝ) :
    (starRingEnd ℂ) (f t) = f t ∧ (starRingEnd ℂ) (f' t) = f' t := by
  have hf₁ : ∀ t, HasDerivAt f (f' t) t ∧
      HasDerivAt f' ((fun _ => (0 : ℝ)) t • f' t + P t • f t) t := fun t =>
    ⟨(hf t).1, (hf t).2.congr_deriv (by simp [Complex.real_smul])⟩
  have hg : ∀ t, HasDerivAt (fun t => star (f t)) (star (f' t)) t ∧
      HasDerivAt (fun t => star (f' t)) ((fun _ => (0 : ℝ)) t • star (f' t) +
        P t • star (f t)) t := fun t =>
    ⟨(hf t).1.star, (hf t).2.star.congr_deriv (by
      simp [Complex.real_smul, Complex.conj_ofReal])⟩
  have := eq_of_linear_ode (t₀ := t₀) continuous_const hP hf₁ hg h0.symm h1.symm
  exact ⟨(congrFun this.1 t).symm, (congrFun this.2 t).symm⟩

end ODE
