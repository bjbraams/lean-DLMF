/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Mathieu.Properties.Spectra

/-!
# Periodicity and normalization of Mathieu eigenfunctions

Periodicity, parity, normalization and orthogonality of the integer-order Mathieu
eigenfunctions.

Source references and common attribution are retained in
`DLMF.Mathieu.Properties`.
-/

@[expose] public noncomputable section

open Complex Set Filter ComplexConjugate

open scoped Topology Real

namespace DLMF.Mathieu

/-! ### Eigenfunctions (§28.2(vi)) -/

/-- `∫₀^{2π} |f|² > 0` for a continuous `f` that is nonzero just to the right of `0`. -/
theorem m28a_integral_normSq_pos {f : ℂ → ℂ} (hf : Continuous f)
    (h0 : ∀ᶠ x : ℝ in 𝓝[>] 0, f x ≠ 0) : 0 < ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2 := by
  have hc : Continuous fun x : ℝ => ‖f x‖ ^ 2 := (hf.comp Complex.continuous_ofReal).norm.pow 2
  obtain ⟨u, hu, hsub0⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h0
  have h2π : (0 : ℝ) < 2 * π := by positivity
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    (Eventually.of_forall fun x => by positivity) (hc.intervalIntegrable _ _)]
  refine ⟨h2π, ?_⟩
  have hsub : Ioo 0 (min u (2 * π)) ⊆
      Function.support (fun x : ℝ => ‖f x‖ ^ 2) ∩ Ioc 0 (2 * π) := by
    intro x hx
    refine ⟨?_, hx.1, le_of_lt (lt_of_lt_of_le hx.2 (min_le_right _ _))⟩
    have : f x ≠ 0 := hsub0 ⟨hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
    simpa [Function.mem_support] using this
  refine lt_of_lt_of_le ?_ (MeasureTheory.measure_mono hsub)
  have hu' : (0 : ℝ) < u := hu
  rw [Real.volume_Ioo]; simp [hu', Real.pi_pos]

/-- `ce_n(0, q) > 0` (the sign convention of `mathieuCe`, DLMF §28.2(vi)). -/
theorem mathieuCeZero_pos (n : ℕ) (q : ℝ) : 0 < mathieuCeZero n q := by
  obtain ⟨h, h0, -⟩ := mathieuWI_spec (mathieuA n q) q
  have hev : ∀ᶠ x : ℝ in 𝓝 0, mathieuWI (mathieuA n q) q x ≠ 0 :=
    (h.differentiable.continuous.comp Complex.continuous_ofReal).continuousAt.eventually_ne
      (by simp [h0])
  exact Real.sqrt_pos.mpr (div_pos Real.pi_pos
    (m28a_integral_normSq_pos h.differentiable.continuous (nhdsWithin_le_nhds hev)))

/-- `se_n'(0, q) > 0` (the sign convention of `mathieuSe`, DLMF §28.2(vi)). -/
theorem mathieuSeDerivZero_pos (n : ℕ) (q : ℝ) : 0 < mathieuSeDerivZero n q := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec (mathieuB n q) q
  have hd : HasDerivAt (fun x : ℝ => mathieuWII (mathieuB n q) q x) 1 0 := by
    have := (h.differentiable _).hasDerivAt.comp_ofReal (z := 0)
    simpa [h1] using this
  have hev := hd.eventually_ne (c := 0) one_ne_zero
  have hev' : ∀ᶠ x : ℝ in 𝓝[>] 0, mathieuWII (mathieuB n q) q x ≠ 0 := by
    exact nhdsWithin_mono (0 : ℝ) (fun x (hx : x ∈ Ioi (0 : ℝ)) => ne_of_gt hx) hev
  exact Real.sqrt_pos.mpr (div_pos Real.pi_pos
    (m28a_integral_normSq_pos h.differentiable.continuous hev'))

/-- **DLMF 28.2.38**: `ce_n(z, q) / ce_n(0, q) = w_I(z; a_n(q), q)`. -/
@[dlmf 28.2.E38]
theorem mathieuCe_div_mathieuCe_zero (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe n z q / mathieuCe n 0 q = mathieuWI (mathieuA n q) q z := by
  rw [mathieuCe_zero, mathieuCe]
  have : (mathieuCeZero n q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mathieuCeZero_pos n q).ne'
  field_simp

/-- **DLMF 28.2.39**: `se_n(z, q) / se_n'(0, q) = w_II(z; b_n(q), q)`. -/
@[dlmf 28.2.E39]
theorem mathieuSe_div_deriv_mathieuSe_zero (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuSe n z q / deriv (fun z => mathieuSe n z q) 0 = mathieuWII (mathieuB n q) q z := by
  rw [deriv_mathieuSe_zero, mathieuSe]
  have : (mathieuSeDerivZero n q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mathieuSeDerivZero_pos n q).ne'
  field_simp

/-! ### Periodicity and parity of the eigenfunctions (Table 28.2.2) -/

section Periodicity

variable {a q : ℂ}

/-- If `w_I'(π/2) = 0` then `w_I` has period `π`. -/
theorem m28a_mathieuWI_periodic (h : deriv (mathieuWI a q) (π / 2) = 0) (z : ℂ) :
    mathieuWI a q (z + π) = mathieuWI a q z := by
  have hW := mathieuWI_wronskian a q (π / 2)
  have e := m28a_mathieuWI_pi_sub a q (-z)
  rw [h] at e hW
  rw [show z + π = π - -z by ring, e, mathieuWI_neg]
  linear_combination mathieuWI a q z * hW

/-- If `w_I(π/2) = 0` then `w_I` has antiperiod `π`. -/
theorem m28a_mathieuWI_antiperiodic (h : mathieuWI a q (π / 2) = 0) (z : ℂ) :
    mathieuWI a q (z + π) = -mathieuWI a q z := by
  have hW := mathieuWI_wronskian a q (π / 2)
  have e := m28a_mathieuWI_pi_sub a q (-z)
  rw [h] at e hW
  rw [show z + π = π - -z by ring, e, mathieuWI_neg]
  linear_combination -(mathieuWI a q z) * hW

/-- If `w_II'(π/2) = 0` then `w_II` has antiperiod `π`. -/
theorem m28a_mathieuWII_antiperiodic (h : deriv (mathieuWII a q) (π / 2) = 0) (z : ℂ) :
    mathieuWII a q (z + π) = -mathieuWII a q z := by
  have hW := mathieuWI_wronskian a q (π / 2)
  have e := m28a_mathieuWII_pi_sub a q (-z)
  rw [h] at e hW
  rw [show z + π = π - -z by ring, e, mathieuWII_neg]
  linear_combination -(mathieuWII a q z) * hW

/-- If `w_II(π/2) = 0` then `w_II` has period `π`. -/
theorem m28a_mathieuWII_periodic (h : mathieuWII a q (π / 2) = 0) (z : ℂ) :
    mathieuWII a q (z + π) = mathieuWII a q z := by
  have hW := mathieuWI_wronskian a q (π / 2)
  have e := m28a_mathieuWII_pi_sub a q (-z)
  rw [h] at e hW
  rw [show z + π = π - -z by ring, e, mathieuWII_neg]
  linear_combination mathieuWII a q z * hW

end Periodicity

/-- **Table 28.2.2**: `ce_n(z, q)` is even. -/
@[dlmf 28.2.T2]
theorem mathieuCe_neg (n : ℕ) (z : ℂ) (q : ℝ) : mathieuCe n (-z) q = mathieuCe n z q := by
  simp [mathieuCe, mathieuWI_neg]

/-- **Table 28.2.2**: `se_n(z, q)` is odd. -/
@[dlmf 28.2.T2]
theorem mathieuSe_neg (n : ℕ) (z : ℂ) (q : ℝ) : mathieuSe n (-z) q = -mathieuSe n z q := by
  simp [mathieuSe, mathieuWII_neg]

/-- **Table 28.2.2**: `ce_{2n}(z, q)` has period `π`. -/
@[dlmf 28.2.T2]
theorem mathieuCe_even_add_pi (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe (2 * n) (z + π) q = mathieuCe (2 * n) z q := by
  simp only [mathieuCe]
  rw [m28a_mathieuWI_periodic (deriv_mathieuWI_half_pi_mathieuA_even n q)]

/-- **Table 28.2.2**: `ce_{2n+1}(z, q)` has antiperiod `π`. -/
@[dlmf 28.2.T2]
theorem mathieuCe_odd_add_pi (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe (2 * n + 1) (z + π) q = -mathieuCe (2 * n + 1) z q := by
  simp only [mathieuCe]
  rw [m28a_mathieuWI_antiperiodic (mathieuWI_half_pi_mathieuA_odd n q)]; ring

/-- **Table 28.2.2**: `se_{2n+1}(z, q)` has antiperiod `π`. -/
@[dlmf 28.2.T2]
theorem mathieuSe_odd_add_pi (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuSe (2 * n + 1) (z + π) q = -mathieuSe (2 * n + 1) z q := by
  simp only [mathieuSe]
  rw [m28a_mathieuWII_antiperiodic (deriv_mathieuWII_half_pi_mathieuB_odd n q)]; ring

/-- **Table 28.2.2**: `se_{2n+2}(z, q)` has period `π`. -/
@[dlmf 28.2.T2]
theorem mathieuSe_even_add_pi (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuSe (2 * n + 2) (z + π) q = mathieuSe (2 * n + 2) z q := by
  simp only [mathieuSe]
  rw [m28a_mathieuWII_periodic (mathieuWII_half_pi_mathieuB_even n q)]

/-! ### Normalization and orthogonality helpers -/

/-- Complex conjugation: `conj ∘ w ∘ conj` solves Mathieu's equation for `(conj a, conj q)`. -/
lemma IsMathieuSolution.p1a1_conj {a q : ℂ} {w : ℂ → ℂ} (h : IsMathieuSolution a q w) :
    IsMathieuSolution (conj a) (conj q) (conj ∘ w ∘ conj) := by
  refine ⟨fun z => ?_, fun z => ?_⟩
  · simpa using (h.differentiable (conj z)).conj_conj
  · rw [deriv_conj_conj]
    have := (h.hasDerivAt_deriv (conj z)).conj_conj
    simp only [Complex.conj_conj] at this
    convert this using 1
    simp only [Function.comp, map_mul, map_sub, map_ofNat, ← Complex.cos_conj, Complex.conj_conj]

/-- `w_I(z; conj a, conj q) = conj (w_I(conj z; a, q))`. -/
lemma p1a1_mathieuWI_conj (a q z : ℂ) :
    mathieuWI (conj a) (conj q) z = conj (mathieuWI a q (conj z)) := by
  obtain ⟨h, h0, h1⟩ := mathieuWI_spec a q
  obtain ⟨g, g0, g1⟩ := mathieuWI_spec (conj a) (conj q)
  have key := g.eq_of_initial h.p1a1_conj (z₀ := 0) (by simp [g0, h0])
    (by rw [deriv_conj_conj]; simp [g1, h1])
  exact congrFun key z

/-- `w_II(z; conj a, conj q) = conj (w_II(conj z; a, q))`. -/
lemma p1a1_mathieuWII_conj (a q z : ℂ) :
    mathieuWII (conj a) (conj q) z = conj (mathieuWII a q (conj z)) := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec a q
  obtain ⟨g, g0, g1⟩ := mathieuWII_spec (conj a) (conj q)
  have key := g.eq_of_initial h.p1a1_conj (z₀ := 0) (by simp [g0, h0])
    (by rw [deriv_conj_conj]; simp [g1, h1])
  exact congrFun key z

/-- `w_I(x; a, q)` is real for real `x`, `a`, `q`. -/
theorem p1a1_mathieuWI_real (a q x : ℝ) : conj (mathieuWI a q x) = mathieuWI a q x := by
  have := p1a1_mathieuWI_conj a q x
  simp only [Complex.conj_ofReal] at this
  exact this.symm

/-- `w_II(x; a, q)` is real for real `x`, `a`, `q`. -/
theorem p1a1_mathieuWII_real (a q x : ℝ) : conj (mathieuWII a q x) = mathieuWII a q x := by
  have := p1a1_mathieuWII_conj a q x
  simp only [Complex.conj_ofReal] at this
  exact this.symm

/-- `w_I'(x; a, q)` is real for real `x`, `a`, `q`. -/
theorem p1a1_deriv_mathieuWI_real (a q x : ℝ) :
    conj (deriv (mathieuWI a q) x) = deriv (mathieuWI a q) x := by
  have e : mathieuWI (a : ℂ) q = conj ∘ mathieuWI (a : ℂ) q ∘ conj := by
    funext z; have := p1a1_mathieuWI_conj a q z; simpa using this
  conv_rhs => rw [e, deriv_conj_conj]
  simp

/-- `w_II'(x; a, q)` is real for real `x`, `a`, `q`. -/
theorem p1a1_deriv_mathieuWII_real (a q x : ℝ) :
    conj (deriv (mathieuWII a q) x) = deriv (mathieuWII a q) x := by
  have e : mathieuWII (a : ℂ) q = conj ∘ mathieuWII (a : ℂ) q ∘ conj := by
    funext z; have := p1a1_mathieuWII_conj a q z; simpa using this
  conv_rhs => rw [e, deriv_conj_conj]
  simp

/-- A real complex number squared is its squared norm. -/
lemma p1a1_sq_eq_norm_sq {z : ℂ} (h : conj z = z) : z ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨r, rfl⟩ := Complex.conj_eq_iff_real.mp h
  simp [Complex.norm_real, sq_abs]

/-- `∫₀^{2π} ‖w_I(x; a, q)‖² > 0`. -/
lemma p1a1_integral_normSq_mathieuWI_pos (a q : ℂ) :
    0 < ∫ x in (0 : ℝ)..2 * π, ‖mathieuWI a q x‖ ^ 2 := by
  obtain ⟨h, h0, -⟩ := mathieuWI_spec a q
  have hev : ∀ᶠ x : ℝ in 𝓝 0, mathieuWI a q x ≠ 0 :=
    (h.differentiable.continuous.comp Complex.continuous_ofReal).continuousAt.eventually_ne
      (by simp [h0])
  exact m28a_integral_normSq_pos h.differentiable.continuous (nhdsWithin_le_nhds hev)

/-- `∫₀^{2π} ‖w_II(x; a, q)‖² > 0`. -/
lemma p1a1_integral_normSq_mathieuWII_pos (a q : ℂ) :
    0 < ∫ x in (0 : ℝ)..2 * π, ‖mathieuWII a q x‖ ^ 2 := by
  obtain ⟨h, h0, h1⟩ := mathieuWII_spec a q
  have hd : HasDerivAt (fun x : ℝ => mathieuWII a q x) 1 0 := by
    have := (h.differentiable _).hasDerivAt.comp_ofReal (z := 0)
    simpa [h1] using this
  have hev := hd.eventually_ne (c := 0) one_ne_zero
  have hev' : ∀ᶠ x : ℝ in 𝓝[>] 0, mathieuWII a q x ≠ 0 :=
    nhdsWithin_mono (0 : ℝ) (fun x (hx : x ∈ Ioi (0 : ℝ)) => ne_of_gt hx) hev
  exact m28a_integral_normSq_pos h.differentiable.continuous hev'

/-- `∫₀^{2π} (c f)² = π` when `f` is real on the real axis and `c = (π / ∫ ‖f‖²)^{1/2}`. -/
theorem p1a1_integral_normalized_sq {f : ℂ → ℂ}
    (hr : ∀ x : ℝ, conj (f x) = f x) (hpos : 0 < ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2) :
    ∫ x in (0 : ℝ)..2 * π,
      ((Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2) : ℂ) * f x) ^ 2 = π := by
  set I := ∫ x in (0 : ℝ)..2 * π, ‖f x‖ ^ 2
  have e : ∀ x : ℝ, ((Real.sqrt (π / I) : ℂ) * f x) ^ 2 =
      (((Real.sqrt (π / I)) ^ 2 * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    intro x; rw [mul_pow, p1a1_sq_eq_norm_sq (hr x)]; push_cast; ring
  simp_rw [e]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    Real.sq_sqrt (div_pos Real.pi_pos hpos).le, div_mul_cancel₀ _ hpos.ne']

/-- `∫₀^{2π} cos²(nx) dx = π`, `n ≠ 0`. -/
theorem p1a1_integral_cos_sq {n : ℕ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..2 * π, Real.cos (n * x) ^ 2 = π := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) hn', integral_cos_sq]
  have : Real.sin (n * (2 * π)) = 0 := by
    rw [show (n : ℝ) * (2 * π) = ((2 * n : ℕ) : ℝ) * π by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  rw [this]; simp; field_simp

/-- `∫₀^{2π} sin²(nx) dx = π`, `n ≠ 0`. -/
theorem p1a1_integral_sin_sq {n : ℕ} (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..2 * π, Real.sin (n * x) ^ 2 = π := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) hn', integral_sin_sq]
  have : Real.sin (n * (2 * π)) = 0 := by
    rw [show (n : ℝ) * (2 * π) = ((2 * n : ℕ) : ℝ) * π by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  rw [this]; simp; field_simp

/-- `‖cos(nx)‖² = cos²(nx)` for real `x`. -/
theorem p1a1_norm_cos_sq (n : ℕ) (x : ℝ) :
    ‖Complex.cos (n * x)‖ ^ 2 = Real.cos (n * x) ^ 2 := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

/-- `‖sin(nx)/n‖² = sin²(nx)/n²` for real `x`. -/
theorem p1a1_norm_sin_div_sq {n : ℕ} (x : ℝ) :
    ‖Complex.sin (n * x) / n‖ ^ 2 = Real.sin (n * x) ^ 2 / (n : ℝ) ^ 2 := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_sin, ← Complex.ofReal_div,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]

/-- `w_I(z; n², 0) = cos nz`. -/
theorem p1a1_mathieuWI_sq_q_zero (n : ℕ) :
    mathieuWI (((n : ℝ) ^ 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) = fun z => Complex.cos (n * z) := by
  funext z; rw [Complex.ofReal_zero]; exact p1a1_mathieuWI_q_zero (by push_cast; ring) z

/-- `w_II(z; n², 0) = sin(nz)/n`, `n ≠ 0`. -/
theorem p1a1_mathieuWII_sq_q_zero {n : ℕ} (hn : n ≠ 0) :
    mathieuWII (((n : ℝ) ^ 2 : ℝ) : ℂ) ((0 : ℝ) : ℂ) = fun z => Complex.sin (n * z) / n := by
  funext z; rw [Complex.ofReal_zero]
  exact p1a1_mathieuWII_q_zero (by push_cast; ring) (Nat.cast_ne_zero.mpr hn) z

/-- **Orthogonality** (Sturm–Liouville): `2π`-periodic solutions of Mathieu's equation for
distinct `a₁ ≠ a₂` (same `q`) are orthogonal on `[0, 2π]`. -/
lemma p1a1_integral_mul_eq_zero {a₁ a₂ q : ℂ} {u v : ℂ → ℂ} (hu : IsMathieuSolution a₁ q u)
    (hv : IsMathieuSolution a₂ q v) (hup : ∀ z, u (z + 2 * π) = u z)
    (hvp : ∀ z, v (z + 2 * π) = v z) (hne : a₁ ≠ a₂) :
    ∫ x in (0 : ℝ)..2 * π, u x * v x = 0 := by
  have hdp : ∀ {w : ℂ → ℂ}, (∀ z, w (z + 2 * π) = w z) → ∀ z, deriv w (z + 2 * π) = deriv w z := by
    intro w hw z
    have := congrArg (fun f => deriv f z) (funext hw)
    simp only [deriv_comp_add_const] at this
    exact this
  have hF : ∀ x : ℝ, HasDerivAt (fun x : ℝ => deriv u x * v x - u x * deriv v x)
      ((a₂ - a₁) * (u x * v x)) x := by
    intro x
    have h1 := ((hu.hasDerivAt_deriv x).mul (hv.differentiable x).hasDerivAt).sub
      ((hu.differentiable x).hasDerivAt.mul (hv.hasDerivAt_deriv x))
    have := h1.comp_ofReal
    convert this using 1; ring
  have hint : IntervalIntegrable (fun x : ℝ => (a₂ - a₁) * (u x * v x)) MeasureTheory.volume
      0 (2 * π) := by
    apply Continuous.intervalIntegrable
    have := hu.differentiable.continuous
    have := hv.differentiable.continuous
    fun_prop
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) hint
  have e2 : ((2 * π : ℝ) : ℂ) = 0 + 2 * π := by push_cast; ring
  rw [e2, hup, hvp, hdp hup, hdp hvp, Complex.ofReal_zero, sub_self,
    intervalIntegral.integral_const_mul] at key
  rcases mul_eq_zero.mp key with h | h
  · exact absurd (sub_eq_zero.mp h).symm hne
  · exact h

/-- `ce_n(z, q)` has period `2π`. -/
lemma p1a1_mathieuCe_add_two_pi (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe n (z + 2 * π) q = mathieuCe n z q := by
  rw [show z + 2 * π = z + π + π by ring]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [mathieuCe_even_add_pi, mathieuCe_even_add_pi]
  · rw [mathieuCe_odd_add_pi, mathieuCe_odd_add_pi, neg_neg]

/-- `se_n(z, q)`, `n ≥ 1`, has period `2π`. -/
lemma p1a1_mathieuSe_add_two_pi {n : ℕ} (hn : n ≠ 0) (z : ℂ) (q : ℝ) :
    mathieuSe n (z + 2 * π) q = mathieuSe n z q := by
  rw [show z + 2 * π = z + π + π by ring]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, mathieuSe_even_add_pi, mathieuSe_even_add_pi]
  · rw [mathieuSe_odd_add_pi, mathieuSe_odd_add_pi, neg_neg]

/-- **DLMF 28.2.29**: `ce_0(z, 0) = 1/√2`. -/
@[dlmf 28.2.E29]
theorem mathieuCe_zero_zero (z : ℂ) : mathieuCe 0 z 0 = 1 / Real.sqrt 2 := by
  have e := p1a1_mathieuWI_sq_q_zero 0
  simp only [Nat.cast_zero, zero_mul, Complex.cos_zero] at e
  rw [mathieuCe, mathieuCeZero, mathieuA_zero 0]
  simp only [Nat.cast_zero] at e ⊢
  rw [e]
  simp only [norm_one, one_pow, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  rw [show π / (2 * π) = (2 : ℝ)⁻¹ by field_simp, Real.sqrt_inv]
  push_cast; ring

/-- **DLMF 28.2.29**: `ce_n(z, 0) = cos nz`, `n = 1, 2, 3, …`. -/
@[dlmf 28.2.E29]
theorem mathieuCe_q_zero {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    mathieuCe n z 0 = Complex.cos (n * z) := by
  rw [mathieuCe, mathieuCeZero, mathieuA_zero n, p1a1_mathieuWI_sq_q_zero n]
  simp only [p1a1_norm_cos_sq, p1a1_integral_cos_sq hn, div_self Real.pi_ne_zero,
    Real.sqrt_one, Complex.ofReal_one, one_mul]

/-- **DLMF 28.2.29**: `se_n(z, 0) = sin nz`, `n = 1, 2, 3, …`. -/
@[dlmf 28.2.E29]
theorem mathieuSe_q_zero {n : ℕ} (hn : n ≠ 0) (z : ℂ) :
    mathieuSe n z 0 = Complex.sin (n * z) := by
  rw [mathieuSe, mathieuSeDerivZero, mathieuB_zero hn, p1a1_mathieuWII_sq_q_zero hn]
  simp only [p1a1_norm_sin_div_sq]
  rw [intervalIntegral.integral_div, p1a1_integral_sin_sq hn]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [show π / (π / (n : ℝ) ^ 2) = (n : ℝ) ^ 2 by field_simp, Real.sqrt_sq (Nat.cast_nonneg n)]
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  push_cast; field_simp

/-- **Normalization** (DLMF 28.2.30): `∫₀^{2π} ce_n(x, q)² dx = π` (real `q`). -/
@[dlmf 28.2.E30]
theorem integral_mathieuCe_sq (n : ℕ) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuCe n x q ^ 2 = π := by
  have := p1a1_integral_normalized_sq (f := mathieuWI (mathieuA n q) q)
    (fun x => p1a1_mathieuWI_real _ _ x) (p1a1_integral_normSq_mathieuWI_pos _ _)
  exact this

/-- **Normalization** (DLMF 28.2.30): `∫₀^{2π} se_n(x, q)² dx = π`, `n ≥ 1` (real `q`). -/
@[dlmf 28.2.E30]
theorem integral_mathieuSe_sq {n : ℕ} (hn : n ≠ 0) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuSe n x q ^ 2 = π := by
  exact p1a1_integral_normalized_sq (f := mathieuWII (mathieuB n q) q)
    (fun x => p1a1_mathieuWII_real _ _ x) (p1a1_integral_normSq_mathieuWII_pos _ _)

/-- **Orthogonality** (DLMF 28.2.31): `∫₀^{2π} ce_m ce_n = 0` for `m ≠ n` (real `q`). -/
@[dlmf 28.2.E31]
theorem integral_mathieuCe_mul_mathieuCe {m n : ℕ} (hmn : m ≠ n) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuCe m x q * mathieuCe n x q = 0 :=
  p1a1_integral_mul_eq_zero (isMathieuSolution_mathieuCe m q) (isMathieuSolution_mathieuCe n q)
    (fun z => p1a1_mathieuCe_add_two_pi m z q) (fun z => p1a1_mathieuCe_add_two_pi n z q)
    (fun h => hmn (p1a1_mathieuA_injective q (by exact_mod_cast h)))

/-- **Orthogonality** (DLMF 28.2.32): `∫₀^{2π} se_m se_n = 0` for `m ≠ n`, `m, n ≥ 1`. -/
@[dlmf 28.2.E32]
theorem integral_mathieuSe_mul_mathieuSe {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m ≠ n)
    (q : ℝ) : ∫ x in (0 : ℝ)..2 * π, mathieuSe m x q * mathieuSe n x q = 0 :=
  p1a1_integral_mul_eq_zero (isMathieuSolution_mathieuSe m q) (isMathieuSolution_mathieuSe n q)
    (fun z => p1a1_mathieuSe_add_two_pi hm z q) (fun z => p1a1_mathieuSe_add_two_pi hn z q)
    (fun h => hmn (p1a1_mathieuB_injective hm hn q (by exact_mod_cast h)))

/-- **Counterexample** to DLMF 28.2.33 as stated for `n = 0` (where `se_0` is a junk value):
at `q = 0`, `∫₀^{2π} ce_0 se_0 ≠ 0`, since `se_0(x, 0)` is a positive multiple of `x`. -/
lemma p1a1_integral_mathieuCe_mul_mathieuSe_zero_ne :
    ∫ x in (0 : ℝ)..2 * π, mathieuCe 0 x 0 * mathieuSe 0 x 0 ≠ 0 := by
  have hB : mathieuB 0 0 = 0 := by simp [mathieuB]
  have hse : ∀ x : ℂ, mathieuSe 0 x 0 = mathieuSeDerivZero 0 0 * x := by
    intro x; rw [mathieuSe, hB]; push_cast; rw [p1a1_mathieuWII_zero_zero]
  simp_rw [mathieuCe_zero_zero, hse]
  have e : ∀ x : ℝ, (1 / (Real.sqrt 2 : ℂ)) * ((mathieuSeDerivZero 0 0 : ℂ) * (x : ℂ)) =
      ((1 / Real.sqrt 2 * mathieuSeDerivZero 0 0 * x : ℝ) : ℂ) := by
    intro x; push_cast; ring
  simp_rw [e]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul, integral_id]
  have h2 : 0 < Real.sqrt 2 := by positivity
  have := mathieuSeDerivZero_pos 0 0
  rw [Complex.ofReal_ne_zero]
  have : 0 < 1 / Real.sqrt 2 * mathieuSeDerivZero 0 0 * (((2 * π) ^ 2 - 0 ^ 2) / 2) := by
    have hπ := Real.pi_pos
    refine mul_pos (mul_pos (by positivity) this) ?_
    nlinarith
  exact this.ne'

/-- **Orthogonality** (DLMF 28.2.33): `∫₀^{2π} ce_m se_n = 0` for `n ≥ 1`. The hypothesis
`n ≠ 0` was added on 2026-10-26: DLMF does not define `se_0`, and for the junk value `n = 0`
the statement fails (`p1a1_integral_mathieuCe_mul_mathieuSe_zero_ne`). -/
@[dlmf 28.2.E33]
theorem integral_mathieuCe_mul_mathieuSe (m n : ℕ) (hn : n ≠ 0) (q : ℝ) :
    ∫ x in (0 : ℝ)..2 * π, mathieuCe m x q * mathieuSe n x q = 0 := by
  set f : ℝ → ℂ := fun x => mathieuCe m x q * mathieuSe n x q
  have hp : Function.Periodic f (2 * π) := fun x => by
    simp only [f]; push_cast
    rw [p1a1_mathieuCe_add_two_pi, p1a1_mathieuSe_add_two_pi hn]
  have hodd : ∀ x, f (-x) = -f x := fun x => by
    simp only [f]; push_cast; rw [mathieuCe_neg, mathieuSe_neg]; ring
  have h1 : ∫ x in (0 : ℝ)..2 * π, f x = ∫ x in (-π)..π, f x := by
    have := hp.intervalIntegral_add_eq 0 (-π)
    rw [zero_add, show -π + 2 * π = π by ring] at this
    exact this
  have h2 : ∫ x in (-π)..π, f x = -∫ x in (-π)..π, f x := by
    have := intervalIntegral.integral_comp_neg (a := -π) (b := π) f
    rw [neg_neg] at this
    conv_lhs => rw [← this]
    simp only [hodd, intervalIntegral.integral_neg]
  show ∫ x in (0 : ℝ)..2 * π, f x = 0
  rw [h1]
  linear_combination h2 / 2

/-- The normalization step of 28.2.34–28.2.37: if `G(z) = c F(π/2 - z)` with `F` continuous and
`2π`-periodic and `(-1)ⁿ c > 0`, then the normalized `G` is `(-1)ⁿ` times the normalized
`F(π/2 - ·)`. -/
lemma p2s_neg_q_aux {F G : ℂ → ℂ} {c : ℝ} {n : ℕ} (hper : ∀ z, F (z + 2 * π) = F z)
    (hFG : ∀ z, G z = c * F (π / 2 - z)) (hs : 0 < (-1) ^ n * c) (z : ℂ) :
    (Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖G x‖ ^ 2) : ℂ) * G z =
      (-1) ^ n * ((Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖F x‖ ^ 2) : ℂ) * F (π / 2 - z)) := by
  set f : ℝ → ℝ := fun y => ‖F y‖ ^ 2
  have hp : Function.Periodic f (2 * π) := fun x => by
    simp only [f]; push_cast; rw [hper]
  have e : ∀ x : ℝ, ‖G x‖ ^ 2 = c ^ 2 * f (π / 2 - x) := fun x => by
    rw [hFG]; simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    push_cast; ring_nf
  have hI : ∫ x in (0 : ℝ)..2 * π, ‖G x‖ ^ 2 = c ^ 2 * ∫ x in (0 : ℝ)..2 * π, ‖F x‖ ^ 2 := by
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left]
    have := hp.intervalIntegral_add_eq (π / 2 - 2 * π) 0
    rw [show π / 2 - 2 * π + 2 * π = π / 2 - 0 by ring, zero_add] at this
    rw [this]
  set J := π / ∫ x in (0 : ℝ)..2 * π, ‖F x‖ ^ 2
  have hc : c ≠ 0 := fun h => by simp [h] at hs
  have key : Real.sqrt (π / ∫ x in (0 : ℝ)..2 * π, ‖G x‖ ^ 2) * c = (-1) ^ n * Real.sqrt J := by
    rw [hI, show π / (c ^ 2 * ∫ x in (0 : ℝ)..2 * π, ‖F x‖ ^ 2) = J / c ^ 2 by
      simp only [J]; field_simp, Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_sq_eq_abs]
    rcases neg_one_pow_eq_or ℝ n with h | h
    · rw [h] at hs ⊢
      rw [abs_of_pos (by linarith)]; field_simp
    · rw [h] at hs ⊢
      rw [abs_of_neg (by linarith)]; field_simp
  have key' := congrArg (fun r : ℝ => (r : ℂ)) key
  push_cast at key'
  rw [hFG]
  linear_combination F (π / 2 - z) * key'

/-- **Change of sign of `q`** (DLMF 28.2.34): `ce_{2n}(z, -q) = (-1)ⁿ ce_{2n}(π/2 - z, q)`. -/
@[dlmf 28.2.E34]
theorem mathieuCe_even_neg_q (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe (2 * n) z (-q) = (-1) ^ n * mathieuCe (2 * n) (π / 2 - z) q := by
  set a := mathieuA (2 * n) q
  obtain ⟨α, hα, hσ⟩ := p2s_sign_A_even n q
  have hA' := deriv_mathieuWI_half_pi_mathieuA_even n q
  obtain ⟨b, hb⟩ : ∃ b : ℝ, deriv (mathieuWII a q) (π / 2) = b :=
    ⟨_, by rw [← p2s_hpi]; exact (p2s_WII_eq a q _).2⟩
  have hW := mathieuWI_wronskian a q (π / 2)
  rw [hα, hA', hb] at hW
  have hαb : α * b = 1 := by exact_mod_cast (by linear_combination hW : (α : ℂ) * b = 1)
  have hK : ∀ z, mathieuWI a (-q) z = b * mathieuWI a q (π / 2 - z) := fun z => by
    rw [← mathieuWI_neg, p1a1_mathieuWI_neg_q, hb, hA', show -z + π / 2 = π / 2 - z by ring]
    ring
  have hper : ∀ z, mathieuWI a q (z + 2 * π) = mathieuWI a q z := fun z => by
    rw [show z + 2 * π = z + π + π by ring, m28a_mathieuWI_periodic hA',
      m28a_mathieuWI_periodic hA']
  have hs : 0 < (-1) ^ n * b := by
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] at hσ ⊢ <;> nlinarith
  simp only [mathieuCe, mathieuCeZero, mathieuA_even_neg, Complex.ofReal_neg]
  exact p2s_neg_q_aux hper hK hs z

/-- **Change of sign of `q`** (DLMF 28.2.35):
`ce_{2n+1}(z, -q) = (-1)ⁿ se_{2n+1}(π/2 - z, q)`. -/
@[dlmf 28.2.E35]
theorem mathieuCe_odd_neg_q (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuCe (2 * n + 1) z (-q) = (-1) ^ n * mathieuSe (2 * n + 1) (π / 2 - z) q := by
  set b := mathieuB (2 * n + 1) q
  obtain ⟨β, hβ, hσ⟩ := p2s_sign_B_odd n q
  have hB' := deriv_mathieuWII_half_pi_mathieuB_odd n q
  obtain ⟨α, hα⟩ : ∃ α : ℝ, deriv (mathieuWI b q) (π / 2) = α :=
    ⟨_, by rw [← p2s_hpi]; exact (p2s_WI_eq b q _).2⟩
  have hW := mathieuWI_wronskian b q (π / 2)
  rw [hβ, hB', hα] at hW
  have hαβ : -α * β = 1 := by exact_mod_cast (by linear_combination hW : -(α : ℂ) * β = 1)
  have hK : ∀ z, mathieuWI b (-q) z = ((-α : ℝ) : ℂ) * mathieuWII b q (π / 2 - z) := fun z => by
    rw [← mathieuWI_neg, p1a1_mathieuWI_neg_q, hB', hα, show -z + π / 2 = π / 2 - z by ring]
    push_cast; ring
  have hper : ∀ z, mathieuWII b q (z + 2 * π) = mathieuWII b q z := fun z => by
    rw [show z + 2 * π = z + π + π by ring, m28a_mathieuWII_antiperiodic hB',
      m28a_mathieuWII_antiperiodic hB', neg_neg]
  have hs : 0 < (-1) ^ n * -α := by
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] at hσ ⊢ <;> nlinarith
  simp only [mathieuCe, mathieuCeZero, mathieuSe, mathieuSeDerivZero, mathieuA_odd_neg,
    Complex.ofReal_neg]
  exact p2s_neg_q_aux hper hK hs z

/-- **Change of sign of `q`** (DLMF 28.2.36):
`se_{2n+1}(z, -q) = (-1)ⁿ ce_{2n+1}(π/2 - z, q)`. -/
@[dlmf 28.2.E36]
theorem mathieuSe_odd_neg_q (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuSe (2 * n + 1) z (-q) = (-1) ^ n * mathieuCe (2 * n + 1) (π / 2 - z) q := by
  set a := mathieuA (2 * n + 1) q
  have hba : mathieuB (2 * n + 1) (-q) = a := by
    have := mathieuA_odd_neg n (-q); rw [neg_neg] at this; exact this.symm
  obtain ⟨α, hα, hσ⟩ := p2s_sign_A_odd n q
  have hA := mathieuWI_half_pi_mathieuA_odd n q
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, mathieuWII a q (π / 2) = β :=
    ⟨_, by rw [← p2s_hpi]; exact (p2s_WII_eq a q _).1⟩
  have hW := mathieuWI_wronskian a q (π / 2)
  rw [hα, hA, hβ] at hW
  have hαβ : -α * β = 1 := by exact_mod_cast (by linear_combination hW : -(α : ℂ) * β = 1)
  have hK : ∀ z, mathieuWII a (-q) z = (β : ℂ) * mathieuWI a q (π / 2 - z) := fun z => by
    have := mathieuWII_neg a (-q) (-z)
    rw [neg_neg] at this
    rw [this, p1a1_mathieuWII_neg_q, hA, hβ, show -z + π / 2 = π / 2 - z by ring]
    ring
  have hper : ∀ z, mathieuWI a q (z + 2 * π) = mathieuWI a q z := fun z => by
    rw [show z + 2 * π = z + π + π by ring, m28a_mathieuWI_antiperiodic hA,
      m28a_mathieuWI_antiperiodic hA, neg_neg]
  have hs : 0 < (-1) ^ n * β := by
    rw [pow_succ] at hσ
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] at hσ ⊢ <;> nlinarith
  simp only [mathieuCe, mathieuCeZero, mathieuSe, mathieuSeDerivZero, hba, Complex.ofReal_neg]
  exact p2s_neg_q_aux hper hK hs z

/-- **Change of sign of `q`** (DLMF 28.2.37):
`se_{2n+2}(z, -q) = (-1)ⁿ se_{2n+2}(π/2 - z, q)`. -/
@[dlmf 28.2.E37]
theorem mathieuSe_even_neg_q (n : ℕ) (z : ℂ) (q : ℝ) :
    mathieuSe (2 * n + 2) z (-q) = (-1) ^ n * mathieuSe (2 * n + 2) (π / 2 - z) q := by
  set b := mathieuB (2 * n + 2) q
  obtain ⟨β, hβ, hσ⟩ := p2s_sign_B_even n q
  have hB := mathieuWII_half_pi_mathieuB_even n q
  obtain ⟨α, hα⟩ : ∃ α : ℝ, mathieuWI b q (π / 2) = α :=
    ⟨_, by rw [← p2s_hpi]; exact (p2s_WI_eq b q _).1⟩
  have hW := mathieuWI_wronskian b q (π / 2)
  rw [hα, hB, hβ] at hW
  have hαβ : α * β = 1 := by exact_mod_cast (by linear_combination hW : (α : ℂ) * β = 1)
  have hK : ∀ z, mathieuWII b (-q) z = ((-α : ℝ) : ℂ) * mathieuWII b q (π / 2 - z) := fun z => by
    have := mathieuWII_neg b (-q) (-z)
    rw [neg_neg] at this
    rw [this, p1a1_mathieuWII_neg_q, hB, hα, show -z + π / 2 = π / 2 - z by ring]
    push_cast; ring
  have hper : ∀ z, mathieuWII b q (z + 2 * π) = mathieuWII b q z := fun z => by
    rw [show z + 2 * π = z + π + π by ring, m28a_mathieuWII_periodic hB,
      m28a_mathieuWII_periodic hB]
  have hs : 0 < (-1) ^ n * -α := by
    rw [pow_succ] at hσ
    rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] at hσ ⊢ <;> nlinarith
  simp only [mathieuSe, mathieuSeDerivZero, mathieuB_even_neg, Complex.ofReal_neg]
  exact p2s_neg_q_aux hper hK hs z

end DLMF.Mathieu

end
