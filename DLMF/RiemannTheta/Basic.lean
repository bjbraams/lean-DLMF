/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.Theta
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Complex.Liouville

/-!
# Riemann theta functions (DLMF §§21.1–21.2)

For a finite index type `ι` (DLMF's genus `g = card ι`), a *Riemann matrix* is a complex
symmetric `ι × ι` matrix whose imaginary part is positive definite (DLMF §21.1); these form
the Siegel upper half-space `siegelUpperHalfSpace ι`. The Riemann theta function
`riemannTheta z Ω = ∑_{n ∈ ℤ^ι} exp(2πi(½ n·Ω·n + n·z))` (DLMF 21.2.1) and the theta function
with real characteristics `riemannThetaChar α β z Ω` (DLMF 21.2.5) are defined as `tsum`s over
the lattice `ι → ℤ`.

The central analytic result of §21.2(i) is proved here: the defining series converges
absolutely, and uniformly on compact subsets of `ℂ^ι × 𝔖_ι`; the limit is continuous there
and holomorphic in each component of `z` and each entry of `Ω`. The proof uses a positive
lower bound for the imaginary quadratic form near a Riemann matrix and a product majorant
built from Mathlib's one-variable bound `summable_pow_mul_jacobiTheta₂_term_bound`.

The `g = 1` case reduces to the one-variable theta functions of DLMF §20.2
(`DLMF.Elliptic.jacobiThetaThreeTau` etc., built on Mathlib's `jacobiTheta₂`), see 21.2.8–12.

`tsum` is totalized: outside the convergence region the defined value is `0`, and all
identities state the hypothesis `Ω ∈ siegelUpperHalfSpace ι` where it is needed.
-/

@[expose] public noncomputable section

open Complex Matrix Finset Filter Topology
open scoped Real

namespace DLMF.RiemannTheta

variable {ι : Type*} [Fintype ι]

/-! ## Riemann matrices and the theta series -/

/-- The Siegel upper half-space: complex symmetric matrices with positive definite imaginary
part, i.e. DLMF's *Riemann matrices* `Ω` (DLMF §21.1, Notation). -/
@[dlmf 21.1 "Riemann matrix: complex symmetric with strictly positive definite imaginary part"]
def siegelUpperHalfSpace (ι : Type*) [Fintype ι] : Set (Matrix ι ι ℂ) :=
  {Ω | Ωᵀ = Ω ∧ (Ω.map Complex.im).PosDef}

/-- The `n`-th term `exp(2πi(½ n·Ω·n + n·z))` of the Riemann theta series (DLMF 21.2.1). -/
def riemannThetaTerm (z : ι → ℂ) (Ω : Matrix ι ι ℂ) (n : ι → ℤ) : ℂ :=
  cexp (2 * π * I * ((1 / 2 : ℂ) * ((fun i => (n i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ))) +
    (fun i => (n i : ℂ)) ⬝ᵥ z))

/-- The Riemann theta function `θ(z|Ω) = ∑_{n ∈ ℤ^g} exp(2πi(½ n·Ω·n + n·z))` (DLMF 21.2.1).
The `tsum` is the genuine sum for `Ω ∈ siegelUpperHalfSpace ι` (`hasSum_riemannTheta`). -/
@[dlmf 21.2.E1]
def riemannTheta (z : ι → ℂ) (Ω : Matrix ι ι ℂ) : ℂ :=
  ∑' n : ι → ℤ, riemannThetaTerm z Ω n

/-- The term of the theta series with characteristics (DLMF 21.2.5):
`exp(2πi(½ [n+α]·Ω·[n+α] + [n+α]·[z+β]))`. -/
def riemannThetaCharTerm (α β : ι → ℝ) (z : ι → ℂ) (Ω : Matrix ι ι ℂ) (n : ι → ℤ) : ℂ :=
  cexp (2 * π * I * ((1 / 2 : ℂ) * ((fun i => (n i : ℂ) + α i) ⬝ᵥ
      (Ω *ᵥ fun i => (n i : ℂ) + α i)) +
    (fun i => (n i : ℂ) + α i) ⬝ᵥ (fun i => z i + β i)))

/-- The Riemann theta function with characteristics `[α; β]`, `α, β ∈ ℝ^g` (DLMF 21.2.5). -/
@[dlmf 21.2.E5]
def riemannThetaChar (α β : ι → ℝ) (z : ι → ℂ) (Ω : Matrix ι ι ℂ) : ℂ :=
  ∑' n : ι → ℤ, riemannThetaCharTerm α β z Ω n

/-- The scaled Riemann theta function
`θ̂(z|Ω) = exp(-π [Im z]·[Im Ω]⁻¹·[Im z]) θ(z|Ω)` (DLMF 21.2.2). -/
@[dlmf 21.2.E2]
def riemannThetaScaled [DecidableEq ι] (z : ι → ℂ) (Ω : Matrix ι ι ℂ) : ℂ :=
  (Real.exp (-π * ((fun i => (z i).im) ⬝ᵥ ((Ω.map Complex.im)⁻¹ *ᵥ fun i => (z i).im))) : ℂ) *
    riemannTheta z Ω

/-- The alternative normalization `Θ(φ|B) = θ(φ/(2πi) | B/(2πi))` (DLMF §21.1). -/
@[dlmf 21.1 "Θ(φ|B) = θ(φ/(2πi)|B/(2πi)); the series form is riemannThetaBig_eq_tsum"]
def riemannThetaBig (φ : ι → ℂ) (B : Matrix ι ι ℂ) : ℂ :=
  riemannTheta (fun i => φ i / (2 * π * I)) ((2 * π * I)⁻¹ • B)

/-! ## The modulus of a term -/

lemma rth21_im_dotProduct_ofReal (x : ι → ℝ) (z : ι → ℂ) :
    ((fun i => (x i : ℂ)) ⬝ᵥ z).im = x ⬝ᵥ fun i => (z i).im := by
  simp [dotProduct, Complex.im_sum]

theorem rth21_im_quad_ofReal (x : ι → ℝ) (Ω : Matrix ι ι ℂ) :
    ((fun i => (x i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (x i : ℂ))).im =
      x ⬝ᵥ (Ω.map Complex.im *ᵥ x) := by
  simp [dotProduct, mulVec, Complex.im_sum, Finset.mul_sum]

omit [Fintype ι] in
lemma rth21_intVec (n : ι → ℤ) : (fun i => (n i : ℂ)) = fun i => (((n i : ℝ)) : ℂ) := by
  simp

/-- `‖exp(2πi(½ n·Ω·n + n·z))‖ = exp(-π n·(Im Ω)·n - 2π n·Im z)`. -/
theorem norm_riemannThetaTerm (z : ι → ℂ) (Ω : Matrix ι ι ℂ) (n : ι → ℤ) :
    ‖riemannThetaTerm z Ω n‖ = Real.exp (-π * ((fun i => (n i : ℝ)) ⬝ᵥ
      (Ω.map Complex.im *ᵥ fun i => (n i : ℝ))) -
        2 * π * ((fun i => (n i : ℝ)) ⬝ᵥ fun i => (z i).im)) := by
  rw [riemannThetaTerm, Complex.norm_exp, rth21_intVec]
  rw [← rth21_im_quad_ofReal, ← rth21_im_dotProduct_ofReal]
  generalize ((fun i => ((n i : ℝ) : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => ((n i : ℝ) : ℂ))) = q
  generalize ((fun i => ((n i : ℝ) : ℂ)) ⬝ᵥ z) = d
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-! ## Convergence (DLMF §21.2(i)) -/

/-- Positivity of the quadratic form of `Im Ω` on nonzero real vectors. This open condition
holds on the Siegel upper half-space and does not require `Ω` to be symmetric. -/
def rth21_PosIm (Ω : Matrix ι ι ℂ) : Prop :=
  ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (Ω.map Complex.im *ᵥ x)

theorem rth21_posIm_of_mem {Ω : Matrix ι ι ℂ} (h : Ω ∈ siegelUpperHalfSpace ι) :
    rth21_PosIm Ω := fun x hx => by
  simpa using h.2.dotProduct_mulVec_pos hx

lemma rth21_exists_lower {Y : Matrix ι ι ℝ} (hY : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (Y *ᵥ x)) :
    ∃ c > 0, ∀ x : ι → ℝ, c * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Y *ᵥ x) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun x => by simp [dotProduct, Finset.univ_eq_empty]⟩
  have hK : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    ⟨fun _ => 1, by simp [mem_sphere_iff_norm, pi_norm_const]⟩
  have hcont : Continuous fun x : ι → ℝ => x ⬝ᵥ (Y *ᵥ x) := by
    simp only [dotProduct, mulVec]
    fun_prop
  obtain ⟨u, hu, hmin⟩ := hK.exists_isMinOn hne hcont.continuousOn
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hm : 0 < u ⬝ᵥ (Y *ᵥ u) := hY u hu0
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  refine ⟨u ⬝ᵥ (Y *ᵥ u) / Fintype.card ι, by positivity, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hv : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simp [norm_smul, hxn.ne']
  have h1 : u ⬝ᵥ (Y *ᵥ u) ≤ (‖x‖⁻¹ • x) ⬝ᵥ (Y *ᵥ (‖x‖⁻¹ • x)) := hmin hv
  rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
  have h4 : u ⬝ᵥ (Y *ᵥ u) * ‖x‖ ^ 2 ≤ x ⬝ᵥ (Y *ᵥ x) := by
    calc u ⬝ᵥ (Y *ᵥ u) * ‖x‖ ^ 2 ≤ (‖x‖⁻¹ * (‖x‖⁻¹ * x ⬝ᵥ (Y *ᵥ x))) * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = x ⬝ᵥ (Y *ᵥ x) := by field_simp
  have h3 : ∑ i, x i ^ 2 ≤ Fintype.card ι * ‖x‖ ^ 2 := by
    calc ∑ i, x i ^ 2 ≤ ∑ _i : ι, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
          have h := norm_le_pi_norm x i
          rw [Real.norm_eq_abs] at h
          nlinarith [abs_nonneg (x i), sq_abs (x i)]
      _ = _ := by simp
  calc u ⬝ᵥ (Y *ᵥ u) / Fintype.card ι * ∑ i, x i ^ 2
      ≤ u ⬝ᵥ (Y *ᵥ u) / Fintype.card ι * (Fintype.card ι * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = u ⬝ᵥ (Y *ᵥ u) * ‖x‖ ^ 2 := by field_simp
    _ ≤ _ := h4

lemma rth21_quad_perturb {Y Y' : Matrix ι ι ℝ} {δ : ℝ} (hδ : ∀ i j, |Y' i j - Y i j| ≤ δ)
    (x : ι → ℝ) :
    x ⬝ᵥ (Y *ᵥ x) - δ * Fintype.card ι * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Y' *ᵥ x) := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
  · simp [dotProduct, Finset.univ_eq_empty]
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ i0 i0)
  have hsplit : x ⬝ᵥ (Y' *ᵥ x) = x ⬝ᵥ (Y *ᵥ x) + x ⬝ᵥ ((Y' - Y) *ᵥ x) := by
    rw [sub_mulVec, dotProduct_sub]
    ring
  have habs : |x ⬝ᵥ ((Y' - Y) *ᵥ x)| ≤ δ * (∑ i, |x i|) ^ 2 := by
    simp only [dotProduct, mulVec, Matrix.sub_apply]
    calc |∑ i, x i * ∑ j, (Y' i j - Y i j) * x j|
        ≤ ∑ i, |x i * ∑ j, (Y' i j - Y i j) * x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |x i| * ∑ j, δ * |x j| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hδ i j) (abs_nonneg _)
      _ = δ * (∑ i, |x i|) ^ 2 := by
          simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
          ring
  have hcs : (∑ i, |x i|) ^ 2 ≤ Fintype.card ι * ∑ i, x i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |x i|)
    simpa [sq_abs] using this
  have := neg_abs_le (x ⬝ᵥ ((Y' - Y) *ᵥ x))
  nlinarith [mul_le_mul_of_nonneg_left hcs hδ0]

/-- The term bound `‖θ-term‖ ≤ ∏ᵢ exp(-π(T nᵢ² - 2S|nᵢ|))`. -/
lemma rth21_norm_term_le {z : ι → ℂ} {Ω : Matrix ι ι ℂ} {T S : ℝ}
    (hY : ∀ x : ι → ℝ, T * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Ω.map Complex.im *ᵥ x))
    (hS : ∀ i, |(z i).im| ≤ S) (n : ι → ℤ) :
    ‖riemannThetaTerm z Ω n‖ ≤ ∏ i, Real.exp (-π * (T * (n i : ℝ) ^ 2 - 2 * S * |(n i : ℝ)|)) := by
  rw [norm_riemannThetaTerm, ← Real.exp_sum, Real.exp_le_exp]
  have h1 := hY (fun i => (n i : ℝ))
  have h2 : -((fun i => (n i : ℝ)) ⬝ᵥ fun i => (z i).im) ≤ S * ∑ i, |(n i : ℝ)| := by
    rw [dotProduct, ← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc -((n i : ℝ) * (z i).im) ≤ |(n i : ℝ)| * |(z i).im| := by
          rw [← abs_mul]; exact neg_le_abs _
      _ ≤ |(n i : ℝ)| * S := mul_le_mul_of_nonneg_left (hS i) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have h3 : ∑ i, -π * (T * (n i : ℝ) ^ 2 - 2 * S * |(n i : ℝ)|) =
      -π * (T * ∑ i, (n i : ℝ) ^ 2) + 2 * π * (S * ∑ i, |(n i : ℝ)|) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_left h1 Real.pi_pos.le,
    mul_le_mul_of_nonneg_left h2 Real.pi_pos.le]

lemma rth21_summable_prod {f : ℤ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hf : Summable f) :
    Summable fun n : ι → ℤ => ∏ i, f (n i) := by
  classical
  refine summable_of_sum_le (c := ∏ _i : ι, ∑' k, f k)
    (fun n => Finset.prod_nonneg fun i _ => hf0 _) fun s => ?_
  calc ∑ n ∈ s, ∏ i, f (n i)
      ≤ ∑ n ∈ Fintype.piFinset (fun i => s.image (fun n : ι → ℤ => n i)), ∏ i, f (n i) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun n hn => Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hn)
          (fun n _ _ => Finset.prod_nonneg fun i _ => hf0 _)
    _ = ∏ i, ∑ k ∈ s.image (fun n : ι → ℤ => n i), f k := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : ι, ∑' k, f k :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun k _ => hf0 k)
          (fun i _ => hf.sum_le_tsum _ (fun k _ => hf0 k))

lemma rth21_eventually_abs_lt {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f)
    (x0 : X) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ x in 𝓝 x0, |f x - f x0| < ε := by
  have := (hf.tendsto x0).eventually (Metric.ball_mem_nhds (f x0) hε)
  filter_upwards [this] with x hx
  simpa [Metric.mem_ball, Real.dist_eq] using hx

/-- Local summable majorant: near a point `(z₀, Ω₀)` with `Im Ω₀` positive definite there is a
summable bound for the theta terms, uniform on a neighbourhood. -/
lemma rth21_local_majorant {z0 : ι → ℂ} {Ω0 : Matrix ι ι ℂ} (h0 : rth21_PosIm Ω0) :
    ∃ t ∈ 𝓝 (z0, Ω0), ∃ u : (ι → ℤ) → ℝ, Summable u ∧
      ∀ p ∈ t, ∀ n, ‖riemannThetaTerm p.1 p.2 n‖ ≤ u n := by
  obtain ⟨c, hc, hlow⟩ := rth21_exists_lower h0
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = c / (2 * (Fintype.card ι + 1)) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδc : δ * Fintype.card ι ≤ c / 2 := by
    rw [hδdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hc]
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = 1 + ∑ i, |(z0 i).im| := ⟨_, rfl⟩
  have ht : {p : (ι → ℂ) × Matrix ι ι ℂ | (∀ i, |(p.1 i).im - (z0 i).im| < 1) ∧
      ∀ i j, |(p.2 i j).im - (Ω0 i j).im| < δ} ∈ 𝓝 (z0, Ω0) := by
    have hA : ∀ᶠ p in 𝓝 (z0, Ω0), ∀ i, |(p.1 i).im - (z0 i).im| < 1 :=
      eventually_all.mpr fun i =>
        rth21_eventually_abs_lt (f := fun p : (ι → ℂ) × Matrix ι ι ℂ => (p.1 i).im)
          (by fun_prop) (z0, Ω0) one_pos
    have hB : ∀ᶠ p in 𝓝 (z0, Ω0), ∀ i j, |(p.2 i j).im - (Ω0 i j).im| < δ :=
      eventually_all.mpr fun i => eventually_all.mpr fun j =>
        rth21_eventually_abs_lt (f := fun p : (ι → ℂ) × Matrix ι ι ℂ => (p.2 i j).im)
          (by fun_prop) (z0, Ω0) hδ
    filter_upwards [hA, hB] with p hpA hpB
    exact ⟨hpA, hpB⟩
  refine ⟨_, ht, fun n => ∏ i, Real.exp (-π * (c / 2 * (n i : ℝ) ^ 2 - 2 * S * |(n i : ℝ)|)),
    ?_, fun p hp n => ?_⟩
  · refine rth21_summable_prod
      (f := fun k : ℤ => Real.exp (-π * (c / 2 * (k : ℝ) ^ 2 - 2 * S * |(k : ℝ)|)))
      (fun k => (Real.exp_pos _).le) ?_
    have hsum := summable_pow_mul_jacobiTheta₂_term_bound S (half_pos hc) 0
    simp only [pow_zero, one_mul, Int.cast_abs] at hsum
    exact hsum
  · refine rth21_norm_term_le (fun x => ?_) (fun i => ?_) n
    · have hp' := rth21_quad_perturb (Y := Ω0.map Complex.im) (Y' := p.2.map Complex.im)
        (δ := δ) (fun i j => by simpa using (hp.2 i j).le) x
      have := hlow x
      have hsq : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hδc hsq]
    · have h1 := hp.1 i
      have h2 : |(z0 i).im| ≤ ∑ i, |(z0 i).im| :=
        Finset.single_le_sum (f := fun i => |(z0 i).im|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ i)
      have h3 := abs_sub_abs_le_abs_sub (p.1 i).im (z0 i).im
      rw [hSdef]
      linarith

/-- Absolute convergence of the Riemann theta series (DLMF §21.2(i)). -/
@[dlmf 21.2.i "absolute convergence of the g-tuple Fourier series"]
theorem summable_norm_riemannThetaTerm (z : ι → ℂ) {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) : Summable fun n => ‖riemannThetaTerm z Ω n‖ := by
  obtain ⟨t, ht, u, hu, hb⟩ := rth21_local_majorant (z0 := z) (rth21_posIm_of_mem hΩ)
  exact hu.of_nonneg_of_le (fun n => norm_nonneg _) (hb (z, Ω) (mem_of_mem_nhds ht))

/-- The theta series sums to `θ(z|Ω)` (DLMF 21.2.1). -/
@[dlmf 21.2.E1]
theorem hasSum_riemannTheta (z : ι → ℂ) {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    HasSum (riemannThetaTerm z Ω) (riemannTheta z Ω) :=
  (summable_norm_riemannThetaTerm z hΩ).of_norm.hasSum

/-- Locally uniform convergence of the theta series on the open set where the quadratic form
of `Im Ω` is positive definite (stronger than DLMF: `Ω` need not be symmetric). -/
@[dlmf 21.2.i "stronger than DLMF: locally uniform where the imaginary quadratic form is positive"]
theorem tendstoLocallyUniformlyOn_riemannTheta :
    TendstoLocallyUniformlyOn (fun (s : Finset (ι → ℤ)) (p : (ι → ℂ) × Matrix ι ι ℂ) =>
        ∑ n ∈ s, riemannThetaTerm p.1 p.2 n) (fun p => riemannTheta p.1 p.2) atTop
      {p | rth21_PosIm p.2} := by
  intro u hu p hp
  obtain ⟨t, ht, v, hv, hb⟩ := rth21_local_majorant (z0 := p.1) (Ω0 := p.2) hp
  exact ⟨t, mem_nhdsWithin_of_mem_nhds ht,
    tendstoUniformlyOn_tsum hv (fun n x hx => hb x hx n) u hu⟩

/-- Uniform convergence of the theta series on compact subsets of `ℂ^g × 𝔖_g`
(DLMF §21.2(i)). -/
@[dlmf 21.2.i "uniform convergence on compact sets of the z and Ω spaces"]
theorem tendstoUniformlyOn_riemannTheta {K : Set ((ι → ℂ) × Matrix ι ι ℂ)} (hK : IsCompact K)
    (hKS : ∀ p ∈ K, p.2 ∈ siegelUpperHalfSpace ι) :
    TendstoUniformlyOn (fun (s : Finset (ι → ℤ)) (p : (ι → ℂ) × Matrix ι ι ℂ) =>
        ∑ n ∈ s, riemannThetaTerm p.1 p.2 n) (fun p => riemannTheta p.1 p.2) atTop K := by
  rw [← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK]
  exact tendstoLocallyUniformlyOn_riemannTheta.mono fun p hp => rth21_posIm_of_mem (hKS p hp)

lemma rth21_continuous_term (n : ι → ℤ) :
    Continuous fun p : (ι → ℂ) × Matrix ι ι ℂ => riemannThetaTerm p.1 p.2 n := by
  simp only [riemannThetaTerm, dotProduct, mulVec]
  fun_prop

/-- `θ(z|Ω)` is jointly continuous on `ℂ^g × 𝔖_g`. -/
@[dlmf 21.2.i "continuity of the locally uniform limit"]
theorem continuousOn_riemannTheta :
    ContinuousOn (fun p : (ι → ℂ) × Matrix ι ι ℂ => riemannTheta p.1 p.2)
      {p | p.2 ∈ siegelUpperHalfSpace ι} := by
  refine (tendstoLocallyUniformlyOn_riemannTheta.mono fun p hp =>
    rth21_posIm_of_mem hp).continuousOn
    (Frequently.of_forall fun s =>
      (continuous_finsetSum _ fun n _ => rth21_continuous_term n).continuousOn)

lemma rth21_differentiableAt_comp {L : ℂ → (ι → ℂ) × Matrix ι ι ℂ} {w0 : ℂ}
    (hL : Continuous L) (h0 : rth21_PosIm (L w0).2)
    (hd : ∀ n, Differentiable ℂ fun w => riemannThetaTerm (L w).1 (L w).2 n) :
    DifferentiableAt ℂ (fun w => riemannTheta (L w).1 (L w).2) w0 := by
  obtain ⟨t, ht, u, hu, hb⟩ := rth21_local_majorant (z0 := (L w0).1) (Ω0 := (L w0).2) h0
  have hpre : L ⁻¹' t ∈ 𝓝 w0 := hL.continuousAt.preimage_mem_nhds ht
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hD := differentiableOn_tsum_of_summable_norm hu (fun n => (hd n).differentiableOn)
    Metric.isOpen_ball (fun n w hw => hb (L w) (hball hw) n)
  exact hD.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))

/-- `θ(z|Ω)` is an analytic function of each component `z_j` (DLMF §21.2(i)). -/
@[dlmf 21.2.i "analytic in each element of z"]
theorem differentiableAt_riemannTheta_update [DecidableEq ι] (z : ι → ℂ) {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) (j : ι) :
    DifferentiableAt ℂ (fun w => riemannTheta (Function.update z j w) Ω) (z j) := by
  have hupd : ∀ w, Function.update z j w = z + (w - z j) • Pi.single j 1 := by
    intro w
    funext i
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  refine rth21_differentiableAt_comp (L := fun w => (Function.update z j w, Ω))
    (by fun_prop) (by simpa using rth21_posIm_of_mem hΩ) fun n => ?_
  simp only [hupd, riemannThetaTerm, dotProduct_add, dotProduct_smul, dotProduct_single,
    smul_eq_mul]
  fun_prop

/-- `θ(z|Ω)` is an analytic function of each entry `Ω_jk`: here the entry `(j,k)` of
`Ω + (w - Ω_jk) E_jk` is `w` (DLMF §21.2(i)). For a symmetric perturbation see the joint
continuity and the parametrization of the entries; the open domain makes the one-entry
perturbation admissible. -/
@[dlmf 21.2.i "analytic in each element of Ω"]
theorem differentiableAt_riemannTheta_entry [DecidableEq ι] (z : ι → ℂ) {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) (j k : ι) :
    DifferentiableAt ℂ (fun w => riemannTheta z (Ω + (w - Ω j k) • Matrix.single j k 1))
      (Ω j k) := by
  refine rth21_differentiableAt_comp
    (L := fun w => (z, Ω + (w - Ω j k) • Matrix.single j k 1))
    (by fun_prop) (by simpa using rth21_posIm_of_mem hΩ) fun n => ?_
  simp only [riemannThetaTerm, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]
  fun_prop

/-! ## The scaled theta function (DLMF 21.2.2) -/

lemma rth21_prod_sum_le {f : ι → ℤ → ℝ} {M : ℝ} (hf0 : ∀ i k, 0 ≤ f i k)
    (hf : ∀ i, Summable (f i)) (hM : ∀ i, ∑' k, f i k ≤ M) :
    Summable (fun n : ι → ℤ => ∏ i, f i (n i)) ∧
      ∑' n : ι → ℤ, ∏ i, f i (n i) ≤ M ^ Fintype.card ι := by
  classical
  have hbound : ∀ s : Finset (ι → ℤ), ∑ n ∈ s, ∏ i, f i (n i) ≤ M ^ Fintype.card ι := by
    intro s
    calc ∑ n ∈ s, ∏ i, f i (n i)
        ≤ ∑ n ∈ Fintype.piFinset (fun i => s.image (fun n : ι → ℤ => n i)), ∏ i, f i (n i) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun n hn => Fintype.mem_piFinset.mpr fun i => Finset.mem_image_of_mem _ hn)
            (fun n _ _ => Finset.prod_nonneg fun i _ => hf0 _ _)
      _ = ∏ i, ∑ k ∈ s.image (fun n : ι → ℤ => n i), f i k := (Finset.prod_univ_sum _ _).symm
      _ ≤ ∏ _i : ι, M :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun k _ => hf0 i k)
            (fun i _ => ((hf i).sum_le_tsum _ (fun k _ => hf0 i k)).trans (hM i))
      _ = M ^ Fintype.card ι := by simp
  have h0 : ∀ n : ι → ℤ, 0 ≤ ∏ i, f i (n i) := fun n => Finset.prod_nonneg fun i _ => hf0 _ _
  exact ⟨summable_of_sum_le h0 hbound, Real.tsum_le_of_sum_le h0 hbound⟩

lemma rth21_gauss_shift_bound {c : ℝ} (hc : 0 < c) :
    ∃ M : ℝ, ∀ t : ℝ, Summable (fun k : ℤ => Real.exp (-π * c * ((k : ℝ) + t) ^ 2)) ∧
      ∑' k : ℤ, Real.exp (-π * c * ((k : ℝ) + t) ^ 2) ≤ M := by
  have hg : Summable fun k : ℤ => Real.exp (-π * c * (k : ℝ) ^ 2) := by
    have := summable_pow_mul_jacobiTheta₂_term_bound 0 hc 0
    simp only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero] at this
    exact this.congr fun k => by ring_nf
  have hg1 : Summable fun k : ℤ => Real.exp (-π * c * ((k : ℝ) + 1) ^ 2) := by
    have := (Equiv.addRight (1 : ℤ)).summable_iff.mpr hg
    exact this.congr fun k => by simp
  refine ⟨∑' k : ℤ, Real.exp (-π * c * (k : ℝ) ^ 2) +
    ∑' k : ℤ, Real.exp (-π * c * ((k : ℝ) + 1) ^ 2), fun t => ?_⟩
  set t' := t - ⌊t⌋ with ht'
  have ht0 : 0 ≤ t' := by simp [ht']
  have ht1 : t' < 1 := by simp only [ht']; linarith [Int.lt_floor_add_one t]
  have hle : ∀ k : ℤ, Real.exp (-π * c * ((k : ℝ) + t') ^ 2) ≤
      Real.exp (-π * c * (k : ℝ) ^ 2) + Real.exp (-π * c * ((k : ℝ) + 1) ^ 2) := by
    intro k
    have hpc : 0 < π * c := mul_pos Real.pi_pos hc
    rcases le_or_gt 0 k with hk | hk
    · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
      have : (k : ℝ) ^ 2 ≤ ((k : ℝ) + t') ^ 2 := by nlinarith
      have h1 : Real.exp (-π * c * ((k : ℝ) + t') ^ 2) ≤ Real.exp (-π * c * (k : ℝ) ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith [Real.exp_pos (-π * c * ((k : ℝ) + 1) ^ 2)]
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + t') ^ 2 := by nlinarith
      have h1 : Real.exp (-π * c * ((k : ℝ) + t') ^ 2) ≤
          Real.exp (-π * c * ((k : ℝ) + 1) ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
      linarith [Real.exp_pos (-π * c * (k : ℝ) ^ 2)]
  have hs' : Summable fun k : ℤ => Real.exp (-π * c * ((k : ℝ) + t') ^ 2) :=
    (hg.add hg1).of_nonneg_of_le (fun k => (Real.exp_pos _).le) hle
  have hshift : ∀ k : ℤ, Real.exp (-π * c * (((k + ⌊t⌋ : ℤ) : ℝ) + t') ^ 2) =
      Real.exp (-π * c * ((k : ℝ) + t) ^ 2) := by
    intro k; simp only [ht']; push_cast; ring_nf
  have hsum : Summable fun k : ℤ => Real.exp (-π * c * ((k : ℝ) + t) ^ 2) := by
    have := (Equiv.addRight ⌊t⌋).summable_iff.mpr hs'
    exact this.congr fun k => by simpa using hshift k
  refine ⟨hsum, ?_⟩
  have heq : ∑' k : ℤ, Real.exp (-π * c * ((k : ℝ) + t) ^ 2) =
      ∑' k : ℤ, Real.exp (-π * c * ((k : ℝ) + t') ^ 2) := by
    calc ∑' k : ℤ, Real.exp (-π * c * ((k : ℝ) + t) ^ 2)
        = ∑' k : ℤ, Real.exp (-π * c * ((((Equiv.addRight ⌊t⌋) k : ℤ) : ℝ) + t') ^ 2) :=
          tsum_congr fun k => by rw [Equiv.coe_addRight, hshift]
      _ = _ := (Equiv.addRight ⌊t⌋).tsum_eq
          (fun k : ℤ => Real.exp (-π * c * ((k : ℝ) + t') ^ 2))
  rw [heq, ← (hg.tsum_add hg1)]
  exact hs'.tsum_le_tsum hle (hg.add hg1)

/-- `θ̂(z|Ω)` is a bounded function of `z` (DLMF §21.2(i), after 21.2.2). -/
@[dlmf 21.2.i "the scaled theta function is bounded in z"]
theorem riemannThetaScaled_bounded [DecidableEq ι] {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) : ∃ C : ℝ, ∀ z : ι → ℂ, ‖riemannThetaScaled z Ω‖ ≤ C := by
  set Y := Ω.map Complex.im with hYdef
  obtain ⟨c, hc, hlow⟩ := rth21_exists_lower (rth21_posIm_of_mem hΩ)
  obtain ⟨M, hM⟩ := rth21_gauss_shift_bound hc
  refine ⟨M ^ Fintype.card ι, fun z => ?_⟩
  set y : ι → ℝ := fun i => (z i).im
  set a : ι → ℝ := Y⁻¹ *ᵥ y
  have hdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hΩ.2.isUnit
  have hYsym : Yᵀ = Y := hΩ.2.isHermitian
  have hYa : Y *ᵥ a = y := by
    simp only [a, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hterm : ∀ n : ι → ℤ, Real.exp (-π * (y ⬝ᵥ (Y⁻¹ *ᵥ y))) * ‖riemannThetaTerm z Ω n‖ ≤
      ∏ i, Real.exp (-π * c * ((n i : ℝ) + a i) ^ 2) := by
    intro n
    rw [norm_riemannThetaTerm, ← Real.exp_add, ← Real.exp_sum, Real.exp_le_exp]
    set N : ι → ℝ := fun i => (n i : ℝ)
    have hq := hlow (N + a)
    have hexp : (N + a) ⬝ᵥ (Y *ᵥ (N + a)) =
        N ⬝ᵥ (Y *ᵥ N) + 2 * (N ⬝ᵥ y) + y ⬝ᵥ (Y⁻¹ *ᵥ y) := by
      have h1 : a ⬝ᵥ (Y *ᵥ N) = N ⬝ᵥ y := by
        rw [dotProduct_mulVec, ← mulVec_transpose, hYsym, hYa, dotProduct_comm]
      rw [mulVec_add, hYa, dotProduct_add, add_dotProduct, add_dotProduct, h1]
      simp only [a]
      rw [dotProduct_comm (Y⁻¹ *ᵥ y) y]
      ring
    have hsum : ∑ i, -π * c * ((n i : ℝ) + a i) ^ 2 = -π * (c * ∑ i, (N + a) i ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [N]; ring
    rw [hsum]
    have : N ⬝ᵥ (Y *ᵥ N) + 2 * (N ⬝ᵥ y) + y ⬝ᵥ (Y⁻¹ *ᵥ y) ≥ c * ∑ i, (N + a) i ^ 2 := by
      rw [← hexp]; exact hq
    nlinarith [Real.pi_pos]
  obtain ⟨hprodS, hprodle⟩ := rth21_prod_sum_le
    (f := fun i k => Real.exp (-π * c * ((k : ℝ) + a i) ^ 2))
    (fun i k => (Real.exp_pos _).le) (fun i => (hM (a i)).1) (fun i => (hM (a i)).2)
  have hS := summable_norm_riemannThetaTerm z hΩ
  rw [riemannThetaScaled, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), riemannTheta]
  calc Real.exp (-π * (y ⬝ᵥ (Y⁻¹ *ᵥ y))) * ‖∑' n, riemannThetaTerm z Ω n‖
      ≤ Real.exp (-π * (y ⬝ᵥ (Y⁻¹ *ᵥ y))) * ∑' n, ‖riemannThetaTerm z Ω n‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hS) (Real.exp_pos _).le
    _ = ∑' n, Real.exp (-π * (y ⬝ᵥ (Y⁻¹ *ᵥ y))) * ‖riemannThetaTerm z Ω n‖ :=
        (tsum_mul_left).symm
    _ ≤ ∑' n : ι → ℤ, ∏ i, Real.exp (-π * c * ((n i : ℝ) + a i) ^ 2) :=
        (hS.mul_left _).tsum_le_tsum hterm hprodS
    _ ≤ M ^ Fintype.card ι := hprodle

section p3t

open MeasureTheory

/-- `∫₀¹ e^{2πikt} dt = δ_{k0}`. -/
lemma p3t_integral_exp_int (k : ℤ) :
    ∫ t in Set.Icc (0 : ℝ) 1, cexp (2 * π * I * k * t) = if k = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  split_ifs with hk
  · subst hk; simp
  · have hc : (2 * π * I * k : ℂ) ≠ 0 := by
      have := Real.pi_ne_zero
      simp [hk, I_ne_zero, this]
    rw [integral_exp_mul_complex hc]
    have : cexp (2 * π * I * k * ((1 : ℝ) : ℂ)) = 1 := by
      rw [ofReal_one, mul_one, show (2 * π * I * k : ℂ) = k * (2 * π * I) by ring]
      exact exp_int_mul_two_pi_mul_I k
    rw [this]; simp

/-- The cube measure on `[0,1]^ι`. -/
noncomputable abbrev p3t_cube (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => volume.restrict (Set.Icc (0 : ℝ) 1)

/-- A theta term at a real vector as a constant times a product. -/
lemma p3t_term_real (Ω : Matrix ι ι ℂ) (n : ι → ℤ) (x : ι → ℝ) :
    riemannThetaTerm (fun i => (x i : ℂ)) Ω n =
      cexp (2 * π * I * ((1 / 2 : ℂ) * ((fun i => (n i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ))))) *
        ∏ i, cexp (2 * π * I * (n i) * x i) := by
  rw [riemannThetaTerm, mul_add, Complex.exp_add, ← Complex.exp_sum]
  congr 2
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `∫_{[0,1]^g}` of a theta term is `δ_{n0}`. -/
lemma p3t_integral_term (Ω : Matrix ι ι ℂ) (n : ι → ℤ) :
    ∫ x, riemannThetaTerm (fun i => (x i : ℂ)) Ω n ∂(p3t_cube ι) = if n = 0 then 1 else 0 := by
  simp_rw [p3t_term_real]
  rw [integral_const_mul]
  rw [integral_fintype_prod_eq_prod (f := fun i (t : ℝ) => cexp (2 * π * I * (n i) * t))]
  simp_rw [p3t_integral_exp_int]
  rw [Finset.prod_boole]
  by_cases hn : n = 0
  · subst hn; simp
  · have : ∃ i, n i ≠ 0 := by
      by_contra h; exact hn (funext fun i => not_not.mp fun hi => h ⟨i, hi⟩)
    simp [hn, this]

/-- The modulus of a theta term at a real vector. -/
lemma p3t_norm_term_real (Ω : Matrix ι ι ℂ) (n : ι → ℤ) (x : ι → ℝ) :
    ‖riemannThetaTerm (fun i => (x i : ℂ)) Ω n‖ = ‖riemannThetaTerm 0 Ω n‖ := by
  rw [norm_riemannThetaTerm, norm_riemannThetaTerm]
  simp

/-- The cube has measure one. -/
lemma p3t_cube_univ : (p3t_cube ι) Set.univ = 1 := by
  rw [p3t_cube, Measure.pi_univ]
  simp

/-- `∫_{[0,1]^g} θ(x|Ω) dx = 1`, so `θ(·|Ω)` is not identically zero. -/
lemma p3t_integral_riemannTheta {Ω : Matrix ι ι ℂ} (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    ∫ x, riemannTheta (fun i => (x i : ℂ)) Ω ∂(p3t_cube ι) = 1 := by
  have hfin : IsFiniteMeasure (p3t_cube ι) := ⟨by rw [p3t_cube_univ]; simp⟩
  have hint : ∀ n, Integrable (fun x : ι → ℝ => riemannThetaTerm (fun i => (x i : ℂ)) Ω n)
      (p3t_cube ι) := by
    intro n
    refine Integrable.of_bound ?_ ‖riemannThetaTerm 0 Ω n‖
      (Eventually.of_forall fun x => (p3t_norm_term_real Ω n x).le)
    refine Continuous.aestronglyMeasurable ?_
    simp only [riemannThetaTerm, dotProduct]
    fun_prop
  have hsum : Summable fun n => ∫ x, ‖riemannThetaTerm (fun i => (x i : ℂ)) Ω n‖ ∂(p3t_cube ι) := by
    simp_rw [p3t_norm_term_real, integral_const, smul_eq_mul]
    exact (summable_norm_riemannThetaTerm 0 hΩ).mul_left _
  simp only [riemannTheta]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [p3t_integral_term]
  exact tsum_ite_eq 0 1

end p3t

/-- `θ̂(z|Ω)` is not an analytic function of `z` (DLMF §21.2(i), after 21.2.2); genus
`g ≥ 1`. -/
@[dlmf 21.2.i "the scaled theta function is nonanalytic in z"]
theorem not_differentiable_riemannThetaScaled [DecidableEq ι] [Nonempty ι] {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    ¬ Differentiable ℂ fun z : ι → ℂ => riemannThetaScaled z Ω := by
  intro hd
  obtain ⟨C, hC⟩ := riemannThetaScaled_bounded hΩ
  have hb : Bornology.IsBounded (Set.range fun z => riemannThetaScaled z Ω) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨C, by rintro _ ⟨z, rfl⟩; exact hC z⟩
  have hconst : ∀ z, riemannThetaScaled z Ω = riemannThetaScaled 0 Ω := fun z =>
    hd.apply_eq_apply_of_bounded hb z 0
  have hreal : ∀ x : ι → ℝ, riemannThetaScaled (fun i => (x i : ℂ)) Ω =
      riemannTheta (fun i => (x i : ℂ)) Ω := by
    intro x
    have h0 : (fun i => ((x i : ℂ)).im) = 0 := by funext i; simp
    rw [riemannThetaScaled, h0]; simp
  have hc1 : riemannThetaScaled 0 Ω = 1 := by
    have h := p3t_integral_riemannTheta hΩ
    have e : (fun x : ι → ℝ => riemannTheta (fun i => (x i : ℂ)) Ω) =
        fun _ => riemannThetaScaled 0 Ω := by
      funext x; rw [← hreal, hconst]
    rw [e, MeasureTheory.integral_const, MeasureTheory.measureReal_def, p3t_cube_univ] at h
    simpa using h
  set Y := Ω.map Complex.im with hY
  have hθ : ∀ z : ι → ℂ, riemannTheta z Ω =
      (Real.exp (π * ((fun i => (z i).im) ⬝ᵥ (Y⁻¹ *ᵥ fun i => (z i).im))) : ℂ) := by
    intro z
    have h := hconst z
    rw [hc1, riemannThetaScaled] at h
    rw [← hY] at h
    have he : (Real.exp (-π * ((fun i => (z i).im) ⬝ᵥ (Y⁻¹ *ᵥ fun i => (z i).im))) : ℂ) *
        (Real.exp (π * ((fun i => (z i).im) ⬝ᵥ (Y⁻¹ *ᵥ fun i => (z i).im))) : ℂ) = 1 := by
      rw [← ofReal_mul, ← Real.exp_add]; simp
    calc riemannTheta z Ω = ((Real.exp (-π * ((fun i => (z i).im) ⬝ᵥ
          (Y⁻¹ *ᵥ fun i => (z i).im))) : ℂ) * riemannTheta z Ω) *
          (Real.exp (π * ((fun i => (z i).im) ⬝ᵥ (Y⁻¹ *ᵥ fun i => (z i).im))) : ℂ) := by
          rw [mul_comm _ (riemannTheta z Ω), mul_assoc, he, mul_one]
      _ = _ := by rw [h, one_mul]
  obtain ⟨j⟩ := ‹Nonempty ι›
  set v : ι → ℂ := Pi.single j 1 with hv
  set g : ℂ → ℂ := fun w => riemannTheta (w • v) Ω with hgdef
  have hg : Differentiable ℂ g := fun w0 =>
    rth21_differentiableAt_comp (L := fun w => (w • v, Ω)) (by fun_prop)
      (rth21_posIm_of_mem hΩ) fun n => by
        simp only [riemannThetaTerm, dotProduct_smul, smul_eq_mul]
        fun_prop
  have him : ∀ w : ℂ, (fun i => ((w • v) i).im) = w.im • (Pi.single j 1 : ι → ℝ) := by
    intro w; funext i
    by_cases h : i = j
    · subst h; simp [hv]
    · simp [hv, h]
  have hgr : ∀ w : ℂ, ∀ t : ℝ, g (w + t) = g w := by
    intro w t
    simp only [hgdef, hθ, him, add_im, ofReal_im, add_zero]
  have hg' : ∀ w, deriv g w = 0 := by
    intro w
    have h1 : HasDerivAt (fun u => g (w + u)) (deriv g w) ((0 : ℝ) : ℂ) := by
      rw [ofReal_zero]
      exact HasDerivAt.comp_const_add w 0 (by rw [add_zero]; exact (hg w).hasDerivAt)
    have h2 := h1.comp_ofReal
    have h3 : (fun t : ℝ => g (w + t)) = fun _ => g w := funext fun t => hgr w t
    rw [h3] at h2
    exact h2.unique (hasDerivAt_const _ _)
  have h4 := is_const_of_deriv_eq_zero hg hg' I 0
  simp only [hgdef, hθ, him, I_im, zero_im, one_smul, zero_smul] at h4
  have h5 : π * ((Pi.single j 1 : ι → ℝ) ⬝ᵥ (Y⁻¹ *ᵥ Pi.single j 1)) = 0 := by
    have := congrArg Complex.re h4
    simp only [ofReal_re, Matrix.mulVec_zero, zero_dotProduct, mul_zero, Real.exp_zero] at this
    exact Real.exp_eq_one_iff _ |>.mp this
  have h6 := hΩ.2.inv.dotProduct_mulVec_pos (x := (Pi.single j 1 : ι → ℝ))
    (by simp)
  rw [star_trivial] at h6
  have := Real.pi_pos
  nlinarith

/-- The series form `Θ(φ|B) = ∑ₙ exp(½ n·B·n + n·φ)` of the alternative normalization
(DLMF §21.1). -/
@[dlmf 21.1 "series form of Θ(φ|B)"]
theorem riemannThetaBig_eq_tsum (φ : ι → ℂ) (B : Matrix ι ι ℂ) :
    riemannThetaBig φ B = ∑' n : ι → ℤ, cexp ((1 / 2 : ℂ) *
      ((fun i => (n i : ℂ)) ⬝ᵥ (B *ᵥ fun i => (n i : ℂ))) + (fun i => (n i : ℂ)) ⬝ᵥ φ) := by
  rw [riemannThetaBig, riemannTheta]
  refine tsum_congr fun n => ?_
  rw [riemannThetaTerm]
  congr 1
  have h : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have h2 : (fun i => φ i / (2 * π * I)) = (2 * π * I)⁻¹ • φ := by
    funext i
    simp [div_eq_inv_mul]
  rw [h2, smul_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp

/-! ## The example of DLMF 21.2.3–21.2.4 and the Riemann matrices of §21.4 -/

/-- The Riemann matrix `[[i, -1/2], [-1/2, i]]` of DLMF 21.2.3 (also `Ω₁` of 21.4.2). -/
@[dlmf 21.2.E3 "the example Riemann matrix"]
def riemannMatrixExample : Matrix (Fin 2) (Fin 2) ℂ := !![I, -1 / 2; -1 / 2, I]

/-- `Ω₁ = [[i, -1/2], [-1/2, i]]` of DLMF 21.4.2 (graphics section; exact matrix retained). -/
@[dlmf 21.4.E2]
theorem riemannMatrixExample_eq_omegaOne :
    riemannMatrixExample = !![I, -1 / 2; -1 / 2, I] := rfl

theorem riemannMatrixExample_map_im : riemannMatrixExample.map Complex.im = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [riemannMatrixExample]

/-- The example matrix is a Riemann matrix. -/
@[dlmf 21.2.E3 "the example matrix lies in the Siegel upper half-space"]
theorem riemannMatrixExample_mem : riemannMatrixExample ∈ siegelUpperHalfSpace (Fin 2) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [riemannMatrixExample]
  · rw [riemannMatrixExample_map_im]
    exact Matrix.PosDef.one

lemma rth21_example_term (z : Fin 2 → ℂ) (n : Fin 2 → ℤ) :
    riemannThetaTerm z riemannMatrixExample n =
      cexp (-π * ((n 0 : ℂ) ^ 2 + (n 1 : ℂ) ^ 2)) * cexp (-I * π * (n 0 * n 1 : ℂ)) *
        cexp (2 * π * I * (n 0 * z 0 + n 1 * z 1)) := by
  rw [riemannThetaTerm, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp [riemannMatrixExample, dotProduct, mulVec, Fin.sum_univ_two]
  ring_nf
  rw [I_sq]
  ring

/-- The double series for the example (DLMF 21.2.3). -/
@[dlmf 21.2.E3]
theorem riemannTheta_example (z₁ z₂ : ℂ) :
    riemannTheta ![z₁, z₂] riemannMatrixExample =
      ∑' n₁ : ℤ, ∑' n₂ : ℤ, cexp (-π * ((n₁ : ℂ) ^ 2 + (n₂ : ℂ) ^ 2)) *
        cexp (-I * π * (n₁ * n₂ : ℂ)) * cexp (2 * π * I * (n₁ * z₁ + n₂ * z₂)) := by
  have hs := (summable_norm_riemannThetaTerm ![z₁, z₂] riemannMatrixExample_mem).of_norm
  rw [riemannTheta, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  have hs' := (finTwoArrowEquiv ℤ).symm.summable_iff.mpr hs
  refine (hs'.tsum_prod).trans ?_
  refine tsum_congr fun n₁ => tsum_congr fun n₂ => ?_
  rw [Function.comp_apply, rth21_example_term]
  simp

/-- The scaled double series for the example (DLMF 21.2.4), `z_j = x_j + i y_j`. -/
@[dlmf 21.2.E4]
theorem riemannThetaScaled_example (x₁ y₁ x₂ y₂ : ℝ) :
    riemannThetaScaled ![x₁ + y₁ * I, x₂ + y₂ * I] riemannMatrixExample =
      ∑' n₁ : ℤ, ∑' n₂ : ℤ, cexp (-π * ((n₁ + y₁ : ℂ) ^ 2) - π * ((n₂ + y₂ : ℂ) ^ 2)) *
        cexp (π * I * (2 * n₁ * x₁ + 2 * n₂ * x₂ - n₁ * n₂)) := by
  rw [riemannThetaScaled, riemannTheta_example, riemannMatrixExample_map_im, inv_one,
    one_mulVec, ← tsum_mul_left]
  refine tsum_congr fun n₁ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun n₂ => ?_
  have hy : ((fun i => ((![x₁ + y₁ * I, x₂ + y₂ * I] : Fin 2 → ℂ) i).im) ⬝ᵥ
      fun i => ((![x₁ + y₁ * I, x₂ + y₂ * I] : Fin 2 → ℂ) i).im) = y₁ ^ 2 + y₂ ^ 2 := by
    simp [dotProduct, Fin.sum_univ_two, sq]
  rw [hy, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- The `3 × 3` Riemann matrix `Ω₂` of DLMF 21.4.3 (graphics section; exact matrix retained). -/
@[dlmf 21.4.E3]
def riemannMatrixOmegaTwo : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-1 / 2 + I, 1 / 2 - 1 / 2 * I, -1 / 2 - 1 / 2 * I;
     1 / 2 - 1 / 2 * I, I, 0;
     -1 / 2 - 1 / 2 * I, 0, I]

/-- `Ω₂` of DLMF 21.4.3 is a Riemann matrix. -/
@[dlmf 21.4.E3 "Ω₂ lies in the Siegel upper half-space"]
theorem riemannMatrixOmegaTwo_mem : riemannMatrixOmegaTwo ∈ siegelUpperHalfSpace (Fin 3) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [riemannMatrixOmegaTwo]
  · refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [riemannMatrixOmegaTwo]
    · have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
        by_contra h
        push Not at h
        exact hx (by ext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2])
      simp [riemannMatrixOmegaTwo, dotProduct, mulVec, Fin.sum_univ_three]
      rcases hx' with h | h | h
      · have := pow_pos (abs_pos.mpr h) 2
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1),
          sq_nonneg (x 2), sq_abs (x 0)]
      · have := pow_pos (abs_pos.mpr h) 2
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1),
          sq_nonneg (x 2), sq_abs (x 1)]
      · have := pow_pos (abs_pos.mpr h) 2
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 - x 2), sq_nonneg (x 1),
          sq_nonneg (x 2), sq_abs (x 2)]

/-! ## Characteristics (DLMF §21.2(ii)) -/

theorem rth21_dot_mulVec_comm {Ω : Matrix ι ι ℂ} (hΩ : Ωᵀ = Ω) (a b : ι → ℂ) :
    a ⬝ᵥ (Ω *ᵥ b) = b ⬝ᵥ (Ω *ᵥ a) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hΩ, dotProduct_comm]

/-- The characteristic term as a multiple of a shifted theta term (DLMF 21.2.6, termwise). -/
theorem riemannThetaCharTerm_eq (α β : ι → ℝ) (z : ι → ℂ) {Ω : Matrix ι ι ℂ} (hΩ : Ωᵀ = Ω)
    (n : ι → ℤ) :
    riemannThetaCharTerm α β z Ω n =
      cexp (2 * π * I * ((1 / 2 : ℂ) * ((fun i => (α i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (α i : ℂ))) +
        (fun i => (α i : ℂ)) ⬝ᵥ (z + fun i => (β i : ℂ)))) *
      riemannThetaTerm (z + Ω *ᵥ (fun i => (α i : ℂ)) + fun i => (β i : ℂ)) Ω n := by
  rw [riemannThetaCharTerm, riemannThetaTerm, ← Complex.exp_add]
  congr 1
  have hv : (fun i => (n i : ℂ) + (α i : ℂ)) = (fun i => (n i : ℂ)) + fun i => (α i : ℂ) := rfl
  have hz : (fun i => z i + (β i : ℂ)) = z + fun i => (β i : ℂ) := rfl
  rw [hv, hz]
  simp only [mulVec_add, dotProduct_add, add_dotProduct]
  rw [rth21_dot_mulVec_comm hΩ (fun i => (α i : ℂ)) (fun i => (n i : ℂ))]
  ring

/-- `θ[α;β](z|Ω) = exp(2πi(½ α·Ω·α + α·[z+β])) θ(z + Ωα + β|Ω)` (DLMF 21.2.6).
Corrected from the printed DLMF formula: the hypothesis `Ωᵀ = Ω` is stated, since the identity
uses `n·Ω·α = α·Ω·n` (DLMF assumes it implicitly through the Siegel space). -/
@[dlmf 21.2.E6]
theorem riemannThetaChar_eq (α β : ι → ℝ) (z : ι → ℂ) {Ω : Matrix ι ι ℂ} (hΩ : Ωᵀ = Ω) :
    riemannThetaChar α β z Ω =
      cexp (2 * π * I * ((1 / 2 : ℂ) * ((fun i => (α i : ℂ)) ⬝ᵥ (Ω *ᵥ fun i => (α i : ℂ))) +
        (fun i => (α i : ℂ)) ⬝ᵥ (z + fun i => (β i : ℂ)))) *
      riemannTheta (z + Ω *ᵥ (fun i => (α i : ℂ)) + fun i => (β i : ℂ)) Ω := by
  rw [riemannThetaChar, riemannTheta, ← tsum_mul_left]
  exact tsum_congr fun n => riemannThetaCharTerm_eq α β z hΩ n

/-- `θ[0;0](z|Ω) = θ(z|Ω)` (DLMF 21.2.7). -/
@[dlmf 21.2.E7]
theorem riemannThetaChar_zero (z : ι → ℂ) (Ω : Matrix ι ι ℂ) :
    riemannThetaChar 0 0 z Ω = riemannTheta z Ω := by
  rw [riemannThetaChar, riemannTheta]
  refine tsum_congr fun n => ?_
  simp [riemannThetaCharTerm, riemannThetaTerm]

/-- The theta series with characteristics converges absolutely for `Ω` in the Siegel space. -/
@[dlmf 21.2.ii "absolute convergence of the series with characteristics"]
theorem summable_norm_riemannThetaCharTerm (α β : ι → ℝ) (z : ι → ℂ) {Ω : Matrix ι ι ℂ}
    (hΩ : Ω ∈ siegelUpperHalfSpace ι) :
    Summable fun n => ‖riemannThetaCharTerm α β z Ω n‖ := by
  simp_rw [riemannThetaCharTerm_eq α β z hΩ.1, norm_mul]
  exact (summable_norm_riemannThetaTerm _ hΩ).mul_left _

/-- The set of half-period characteristics `[α; β]`, `αᵢ, βᵢ ∈ {0, ½}` (DLMF §21.2(ii)). -/
@[dlmf 21.2.ii "half-period characteristics"]
def halfPeriodCharacteristics (ι : Type*) : Set ((ι → ℝ) × (ι → ℝ)) :=
  {c | ∀ i, (c.1 i = 0 ∨ c.1 i = 1 / 2) ∧ (c.2 i = 0 ∨ c.2 i = 1 / 2)}

/-- There are `2^{2g}` half-period characteristics (DLMF §21.2(ii)). -/
@[dlmf 21.2.ii "there are 2^(2g) half-period characteristics"]
theorem ncard_halfPeriodCharacteristics [DecidableEq ι] :
    (halfPeriodCharacteristics ι).ncard = 2 ^ (2 * Fintype.card ι) := by
  let e : (ι → Bool) × (ι → Bool) → (ι → ℝ) × (ι → ℝ) := fun b =>
    (fun i => if b.1 i then 1 / 2 else 0, fun i => if b.2 i then 1 / 2 else 0)
  have he : Function.Injective e := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [e, Prod.mk.injEq] at h
    have h1 := h.1
    have h2 := h.2
    ext i
    · have := congrFun h1 i
      rcases Bool.eq_false_or_eq_true (a i) with ha | ha <;>
        rcases Bool.eq_false_or_eq_true (c i) with hc | hc <;> simp [ha, hc] at this ⊢
    · have := congrFun h2 i
      rcases Bool.eq_false_or_eq_true (b i) with ha | ha <;>
        rcases Bool.eq_false_or_eq_true (d i) with hc | hc <;> simp [ha, hc] at this ⊢
  have hrange : halfPeriodCharacteristics ι = Set.range e := by
    ext ⟨α, β⟩
    constructor
    · intro h
      refine ⟨(fun i => decide (α i = 1 / 2), fun i => decide (β i = 1 / 2)), ?_⟩
      simp only [e, Prod.mk.injEq]
      constructor <;> funext i
      · rcases (h i).1 with h' | h' <;> simp only at h' <;> simp [h']
      · rcases (h i).2 with h' | h' <;> simp only at h' <;> simp [h']
    · rintro ⟨⟨a, b⟩, hab⟩
      simp only [e, Prod.mk.injEq] at hab
      intro i
      rw [← hab.1, ← hab.2]
      constructor
      · cases a i <;> simp
      · cases b i <;> simp
  rw [hrange, ← Set.image_univ, Set.ncard_image_of_injective _ he, Set.ncard_univ,
    Nat.card_eq_fintype_card]
  simp [Fintype.card_prod, Fintype.card_bool, pow_mul, sq, ← mul_pow]

/-! ## Relation to the classical theta functions (DLMF §21.2(iii)) -/

open DLMF.Elliptic

lemma rth21_tsum_fin_one (f : (Fin 1 → ℤ) → ℂ) : ∑' n, f n = ∑' k : ℤ, f fun _ => k := by
  rw [← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
  rfl

/-- `θ(z|Ω) = θ₃(πz|Ω)` for `g = 1` (DLMF 21.2.8). -/
@[dlmf 21.2.E8]
theorem riemannTheta_fin_one (z τ : ℂ) :
    riemannTheta ![z] !![τ] = jacobiThetaThreeTau (π * z) τ := by
  rw [riemannTheta, rth21_tsum_fin_one, jacobiThetaThreeTau_eq_tsum]
  refine tsum_congr fun k => ?_
  simp only [riemannThetaTerm]
  congr 1
  simp [dotProduct, mulVec]
  ring

/-- Characteristics in genus one reduce to a shifted `θ₃`. -/
lemma rth21_char_fin_one (a b : ℝ) (z τ : ℂ) :
    riemannThetaChar ![a] ![b] ![z] !![τ] =
      cexp (2 * π * I * ((1 / 2 : ℂ) * (a * (τ * a)) + a * (z + b))) *
        jacobiThetaThreeTau (π * (z + τ * a + b)) τ := by
  rw [riemannThetaChar_eq _ _ _ (by ext i j; fin_cases i; fin_cases j; rfl),
    ← riemannTheta_fin_one]
  congr 2
  · simp [dotProduct]
  · ext i
    fin_cases i
    simp [dotProduct]

/-- `θ₁(πz|Ω) = -θ[½;½](z|Ω)` for `g = 1` (DLMF 21.2.9). -/
@[dlmf 21.2.E9]
theorem jacobiThetaOneTau_eq_riemannThetaChar (z τ : ℂ) :
    jacobiThetaOneTau (π * z) τ = -riemannThetaChar ![1 / 2] ![1 / 2] ![z] !![τ] := by
  rw [rth21_char_fin_one, jacobiThetaOneTau, jacobiThetaTwoTau]
  push_cast
  congr 2
  · congr 1
    ring
  · congr 1
    ring

/-- `θ₂(πz|Ω) = θ[½;0](z|Ω)` for `g = 1` (DLMF 21.2.10). -/
@[dlmf 21.2.E10]
theorem jacobiThetaTwoTau_eq_riemannThetaChar (z τ : ℂ) :
    jacobiThetaTwoTau (π * z) τ = riemannThetaChar ![1 / 2] ![0] ![z] !![τ] := by
  rw [rth21_char_fin_one, jacobiThetaTwoTau]
  push_cast
  congr 1
  · congr 1
    ring
  · congr 1
    ring

/-- `θ₃(πz|Ω) = θ[0;0](z|Ω)` for `g = 1` (DLMF 21.2.11). -/
@[dlmf 21.2.E11]
theorem jacobiThetaThreeTau_eq_riemannThetaChar (z τ : ℂ) :
    jacobiThetaThreeTau (π * z) τ = riemannThetaChar ![0] ![0] ![z] !![τ] := by
  rw [rth21_char_fin_one]
  simp

/-- `θ₄(πz|Ω) = θ[0;½](z|Ω)` for `g = 1` (DLMF 21.2.12). -/
@[dlmf 21.2.E12]
theorem jacobiThetaFourTau_eq_riemannThetaChar (z τ : ℂ) :
    jacobiThetaFourTau (π * z) τ = riemannThetaChar ![0] ![1 / 2] ![z] !![τ] := by
  rw [rth21_char_fin_one, jacobiThetaFourTau]
  push_cast
  simp only [mul_zero, zero_mul, add_zero, Complex.exp_zero, one_mul]
  congr 1
  ring

end DLMF.RiemannTheta
