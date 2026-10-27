/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elliptic.AGM
public import DLMF.Elliptic.Theta

/-!
# Theta functions and the AGM: `K = (π/2) θ₃²` (Temme §12.3.2, DLMF 20.9.2)

For a real nome `0 < q < 1` let `θ₃(q) = ∑ q^{n²}` and `θ₄(q) = ∑ (-1)ⁿ q^{n²}`, the values at
`z = 0` of the DLMF theta functions with `q = e^{iπτ}` (`jacobiThetaThreeTau_zero_I_mul`). Splitting
`ℤ²` into the sublattice `a + b` even, parametrized by `(u+v, u-v)`, and its complement, on which
`(a,b) ↦ (b,a)` cancels the signed terms, gives the doubling identities
`θ₃(q)² + θ₄(q)² = 2θ₃(q²)²` and `θ₃(q) θ₄(q) = θ₄(q²)²`. Hence `(θ₃(q^{2ⁿ})², θ₄(q^{2ⁿ})²)` is an
AGM sequence. It tends to `(1, 1)`, so `M(θ₃², θ₄²) = 1`, and Gauss's theorem gives Jacobi's
`K(m) = (π/2) θ₃(q)²` with complementary modulus `k' = θ₄(q)²/θ₃(q)²`.
-/

@[expose] public section

open Real Set Filter
open scoped Topology

noncomputable section

namespace DLMF.Elliptic

/-- Real `θ₃(q) = ∑_{n∈ℤ} q^{n²}` for `0 < q < 1`. -/
def Real.jacobiThetaThreeNullQ (q : ℝ) : ℝ := ∑' n : ℤ, q ^ (n ^ 2)

/-- Real `θ₄(q) = ∑_{n∈ℤ} (-1)ⁿ q^{n²}` for `0 < q < 1`. -/
def Real.jacobiThetaFourNullQ (q : ℝ) : ℝ := ∑' n : ℤ, (-1 : ℝ) ^ n * q ^ (n ^ 2)

/-- `q^{n²} ≤ q^{|n|}` for `0 < q ≤ 1`. -/
theorem zpow_sq_le {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (n : ℤ) : q ^ (n ^ 2) ≤ q ^ |n| := by
  apply zpow_le_zpow_right_of_le_one₀ hq0 hq1
  rw [← sq_abs]; nlinarith [abs_nonneg n]

/-- `∑_{n∈ℤ} q^{|n|}` converges for `0 < q < 1`. -/
theorem summable_zpow_abs {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : Summable fun n : ℤ => q ^ |n| := by
  apply Summable.of_nat_of_neg <;>
  · simp only [abs_neg, Nat.abs_cast, zpow_natCast]
    exact summable_geometric_of_lt_one hq0.le hq1

/-- `∑_{n∈ℤ} q^{n²}` converges for `0 < q < 1`. -/
theorem summable_zpow_sq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : Summable fun n : ℤ => q ^ (n ^ 2) :=
  (summable_zpow_abs hq0 hq1).of_nonneg_of_le (fun _ => (zpow_pos hq0 _).le)
    (zpow_sq_le hq0 hq1.le)

/-- `∑_{n∈ℤ} (-1)ⁿ q^{n²}` converges absolutely for `0 < q < 1`. -/
theorem summable_neg_one_zpow_mul {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun n : ℤ => (-1 : ℝ) ^ n * q ^ (n ^ 2) := by
  refine (summable_zpow_sq hq0 hq1).of_norm_bounded fun n => ?_
  rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
    Real.norm_of_nonneg (zpow_pos hq0 _).le]

/-- The even sublattice `{(a,b) : a + b even}` is parametrized by `(u,v) ↦ (u+v, u-v)`. -/
def evenLatticeEquiv : ℤ × ℤ ≃ {p : ℤ × ℤ // Even (p.1 + p.2)} where
  toFun uv := ⟨(uv.1 + uv.2, uv.1 - uv.2), ⟨uv.1, by ring⟩⟩
  invFun p := ((p.1.1 + p.1.2) / 2, (p.1.1 - p.1.2) / 2)
  left_inv uv := by
    simp only
    rw [show uv.1 + uv.2 + (uv.1 - uv.2) = 2 * uv.1 by ring,
      show uv.1 + uv.2 - (uv.1 - uv.2) = 2 * uv.2 by ring]
    simp
  right_inv p := by
    obtain ⟨⟨a, b⟩, ⟨r, hr⟩⟩ := p
    simp only at hr ⊢
    have h1 : (a + b) / 2 = r := by rw [hr]; omega
    have h2 : (a - b) / 2 = r - b := by omega
    ext <;> simp [h1, h2]; omega

/-- The swap `(a,b) ↦ (b,a)` on the odd sublattice. -/
def oddLatticeSwap : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)} ≃ {p : ℤ × ℤ // ¬ Even (p.1 + p.2)} where
  toFun p := ⟨(p.1.2, p.1.1), by rw [add_comm]; exact p.2⟩
  invFun p := ⟨(p.1.2, p.1.1), by rw [add_comm]; exact p.2⟩
  left_inv p := rfl
  right_inv p := rfl

/-- `(-1)^a (-1)^b = (-1)^{a+b}`. -/
theorem neg_one_zpow_add (a b : ℤ) : (-1 : ℝ) ^ a * (-1 : ℝ) ^ b = (-1 : ℝ) ^ (a + b) :=
  (zpow_add₀ (by norm_num) a b).symm

/-- `q^{(u+v)²} q^{(u-v)²} = (q²)^{u²} (q²)^{v²}`. -/
theorem zpow_lattice {q : ℝ} (hq0 : 0 < q) (u v : ℤ) :
    q ^ ((u + v) ^ 2) * q ^ ((u - v) ^ 2) = (q ^ 2) ^ (u ^ 2) * (q ^ 2) ^ (v ^ 2) := by
  rw [← zpow_add₀ hq0.ne', ← zpow_add₀ (by positivity), ← zpow_natCast, ← zpow_mul]
  congr 1; push_cast; ring

/-- `θ₃(q)² + θ₄(q)² = 2 θ₃(q²)²`. -/
theorem Real.jacobiThetaThreeNullQ_sq_add_jacobiThetaFourNullQ_sq {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) :
    Real.jacobiThetaThreeNullQ q ^ 2 + Real.jacobiThetaFourNullQ q ^ 2 =
      2 * Real.jacobiThetaThreeNullQ (q ^ 2) ^ 2 := by
  have hs3 := summable_zpow_sq hq0 hq1
  have hs4 := summable_neg_one_zpow_mul hq0 hq1
  have hq2 : 0 < q ^ 2 := by positivity
  have hq21 : q ^ 2 < 1 := by nlinarith
  have hs3' := summable_zpow_sq hq2 hq21
  have h33 := tsum_mul_tsum_of_summable_norm hs3.norm hs3.norm
  have h44 := tsum_mul_tsum_of_summable_norm hs4.norm hs4.norm
  have h33' := tsum_mul_tsum_of_summable_norm hs3'.norm hs3'.norm
  have hP3 := summable_mul_of_summable_norm hs3.norm hs3.norm
  have hP4 := summable_mul_of_summable_norm hs4.norm hs4.norm
  set H : ℤ × ℤ → ℝ := fun p => q ^ (p.1 ^ 2) * q ^ (p.2 ^ 2) +
    (-1 : ℝ) ^ p.1 * q ^ (p.1 ^ 2) * ((-1 : ℝ) ^ p.2 * q ^ (p.2 ^ 2)) with hH
  have hHs : Summable H := hP3.add hP4
  rw [Real.jacobiThetaThreeNullQ, Real.jacobiThetaFourNullQ, Real.jacobiThetaThreeNullQ, sq, sq, sq,
      h33, h44, h33', ← hP3.tsum_add hP4]
  change ∑' p, H p = _
  rw [← hHs.tsum_subtype_add_tsum_subtype_compl {p : ℤ × ℤ | Even (p.1 + p.2)}]
  have hodd : ∀ p : ↥({p : ℤ × ℤ | Even (p.1 + p.2)}ᶜ), H p = 0 := by
    rintro ⟨⟨a, b⟩, hp⟩
    simp only [mem_compl_iff, mem_ofPred_eq, Int.not_even_iff_odd] at hp
    simp only [hH]
    rw [mul_mul_mul_comm, neg_one_zpow_add, hp.neg_one_zpow]
    ring
  rw [tsum_congr hodd, tsum_zero, add_zero, ← tsum_mul_left]
  rw [show (∑' p : ↥{p : ℤ × ℤ | Even (p.1 + p.2)}, H p) =
      ∑' p : {p : ℤ × ℤ // Even (p.1 + p.2)}, H p from rfl, ← evenLatticeEquiv.tsum_eq]
  refine tsum_congr fun uv => ?_
  simp only [evenLatticeEquiv, Equiv.coe_fn_mk, hH]
  rw [mul_mul_mul_comm, neg_one_zpow_add, show uv.1 + uv.2 + (uv.1 - uv.2) = 2 * uv.1 by ring,
    zpow_mul, show ((-1 : ℝ) ^ (2 : ℤ)) = 1 by norm_num, one_zpow, one_mul, zpow_lattice hq0]
  ring

/-- `θ₃(q) θ₄(q) = θ₄(q²)²`. -/
@[dlmf 20.7.E11 "special case z = 0, real nome 0 < q < 1: θ₃(0,q)θ₄(0,q) = θ₄²(0,q²)"]
theorem Real.jacobiThetaThreeNullQ_mul_jacobiThetaFourNullQ {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Real.jacobiThetaThreeNullQ q * Real.jacobiThetaFourNullQ q =
      Real.jacobiThetaFourNullQ (q ^ 2) ^ 2 := by
  have hs3 := summable_zpow_sq hq0 hq1
  have hs4 := summable_neg_one_zpow_mul hq0 hq1
  have hq2 : 0 < q ^ 2 := by positivity
  have hq21 : q ^ 2 < 1 := by nlinarith
  have hs4' := summable_neg_one_zpow_mul hq2 hq21
  have h34 := tsum_mul_tsum_of_summable_norm hs3.norm hs4.norm
  have h44' := tsum_mul_tsum_of_summable_norm hs4'.norm hs4'.norm
  set H : ℤ × ℤ → ℝ := fun p => q ^ (p.1 ^ 2) * ((-1 : ℝ) ^ p.2 * q ^ (p.2 ^ 2)) with hH
  have hHs : Summable H := by
    have := summable_mul_of_summable_norm hs3.norm hs4.norm
    exact this
  rw [Real.jacobiThetaThreeNullQ, Real.jacobiThetaFourNullQ, Real.jacobiThetaFourNullQ, sq, h34,
      h44']
  change ∑' p, H p = _
  rw [← hHs.tsum_subtype_add_tsum_subtype_compl {p : ℤ × ℤ | Even (p.1 + p.2)}]
  have hodd : ∑' p : ↥({p : ℤ × ℤ | Even (p.1 + p.2)}ᶜ), H p = 0 := by
    have hpt : ∀ p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)},
        H (oddLatticeSwap p).1 = -H p.1 := by
      rintro ⟨⟨a, b⟩, hp⟩
      have hp' : Odd (a + b) := Int.not_even_iff_odd.mp hp
      have h1 := neg_one_zpow_add a b
      rw [hp'.neg_one_zpow] at h1
      have h2 : (-1 : ℝ) ^ b * (-1 : ℝ) ^ b = 1 := by
        rw [neg_one_zpow_add, ← two_mul, zpow_mul]; norm_num
      have hsign : (-1 : ℝ) ^ a = -(-1 : ℝ) ^ b := by
        linear_combination (-1 : ℝ) ^ b * h1 - (-1 : ℝ) ^ a * h2
      show q ^ (b ^ 2) * ((-1 : ℝ) ^ a * q ^ (a ^ 2)) =
        -(q ^ (a ^ 2) * ((-1 : ℝ) ^ b * q ^ (b ^ 2)))
      rw [hsign]; ring
    have h := oddLatticeSwap.tsum_eq (fun p => H p.1)
    simp only [hpt, tsum_neg] at h
    change ∑' p : {p : ℤ × ℤ // ¬ Even (p.1 + p.2)}, H p.1 = 0
    linarith
  rw [hodd, add_zero]
  rw [show (∑' p : ↥{p : ℤ × ℤ | Even (p.1 + p.2)}, H p) =
      ∑' p : {p : ℤ × ℤ // Even (p.1 + p.2)}, H p from rfl, ← evenLatticeEquiv.tsum_eq]
  refine tsum_congr fun uv => ?_
  simp only [evenLatticeEquiv, Equiv.coe_fn_mk, hH]
  have hsign : (-1 : ℝ) ^ (uv.1 - uv.2) = (-1 : ℝ) ^ uv.1 * (-1 : ℝ) ^ uv.2 := by
    rw [sub_eq_add_neg, ← neg_one_zpow_add, zpow_neg, ← inv_zpow, inv_neg, inv_one]
  rw [hsign]
  have hl := zpow_lattice hq0 uv.1 uv.2
  linear_combination ((-1 : ℝ) ^ uv.1 * (-1 : ℝ) ^ uv.2) * hl


/-- `r^{n²}` as a natural power. -/
theorem zpow_sq_eq_pow (r : ℝ) (n : ℤ) : r ^ (n ^ 2) = r ^ (n.natAbs ^ 2) := by
  rw [← zpow_natCast]; congr 1; push_cast; rw [sq_abs]

/-- Theta-type series are continuous on `[0, 1/2]` (Weierstrass M-test). -/
theorem continuousOn_tsum_zpow_sq (c : ℤ → ℝ) (hc : ∀ n, |c n| ≤ 1) :
    ContinuousOn (fun r : ℝ => ∑' n : ℤ, c n * r ^ (n ^ 2)) (Icc 0 (1 / 2)) := by
  refine continuousOn_tsum (u := fun n : ℤ => (1 / 2 : ℝ) ^ |n|) (fun n => ?_)
    (summable_zpow_abs (by norm_num) (by norm_num)) (fun n r hr => ?_)
  · simp_rw [zpow_sq_eq_pow]; fun_prop
  · rw [norm_mul, Real.norm_eq_abs, norm_zpow, Real.norm_of_nonneg hr.1]
    have h0 : 0 ≤ r ^ (n ^ 2) := zpow_nonneg hr.1 _
    have h1 : r ^ (n ^ 2) ≤ (1 / 2 : ℝ) ^ (n ^ 2) := by
      rw [zpow_sq_eq_pow, zpow_sq_eq_pow]; exact pow_le_pow_left₀ hr.1 hr.2 _
    calc |c n| * r ^ (n ^ 2) ≤ 1 * r ^ (n ^ 2) := by gcongr; exact hc n
      _ ≤ (1 / 2) ^ |n| := by
          rw [one_mul]; exact h1.trans (zpow_sq_le (by norm_num) (by norm_num) n)

/-- At `r = 0` only the `n = 0` term survives. -/
theorem tsum_zpow_sq_zero (c : ℤ → ℝ) : ∑' n : ℤ, c n * (0 : ℝ) ^ (n ^ 2) = c 0 := by
  rw [tsum_eq_single 0 fun n hn => by
    rw [zero_zpow _ (pow_ne_zero 2 hn), mul_zero]]
  simp

/-- Theta-type series tend to their constant term as `r → 0⁺`. -/
theorem tendsto_tsum_zpow_sq (c : ℤ → ℝ) (hc : ∀ n, |c n| ≤ 1) :
    Tendsto (fun r : ℝ => ∑' n : ℤ, c n * r ^ (n ^ 2)) (𝓝[>] 0) (𝓝 (c 0)) := by
  have h := (continuousOn_tsum_zpow_sq c hc) 0 ⟨le_rfl, by norm_num⟩
  rw [ContinuousWithinAt, tsum_zpow_sq_zero] at h
  exact h.mono_left (nhdsWithin_le_of_mem
    (mem_of_superset (Ico_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)) Ico_subset_Icc_self))

/-- `θ₃(r) → 1` as `r → 0⁺`. -/
theorem Real.tendsto_jacobiThetaThreeNullQ : Tendsto Real.jacobiThetaThreeNullQ (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_tsum_zpow_sq (fun _ => (1 : ℝ)) (fun _ => by simp)
  unfold Real.jacobiThetaThreeNullQ; simpa using h

/-- `θ₄(r) → 1` as `r → 0⁺`. -/
theorem Real.tendsto_jacobiThetaFourNullQ : Tendsto Real.jacobiThetaFourNullQ (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_tsum_zpow_sq (fun n => (-1 : ℝ) ^ n) (fun n => by
    rw [abs_zpow, abs_neg, abs_one, one_zpow])
  unfold Real.jacobiThetaFourNullQ; simpa using h

/-- `θ₃(q) ≥ 1`. -/
theorem Real.one_le_jacobiThetaThreeNullQ {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    1 ≤ Real.jacobiThetaThreeNullQ q := by
  have h := (summable_zpow_sq hq0 hq1).le_tsum 0 (fun n _ => (zpow_pos hq0 _).le)
  unfold Real.jacobiThetaThreeNullQ; simpa using h

/-- `θ₄(q) ≥ 0`, from `θ₃(q) θ₄(q) = θ₄(q²)²`. -/
theorem Real.jacobiThetaFourNullQ_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ Real.jacobiThetaFourNullQ q := by
  have h := Real.jacobiThetaThreeNullQ_mul_jacobiThetaFourNullQ hq0 hq1
  have h3 := Real.one_le_jacobiThetaThreeNullQ hq0 hq1
  by_contra hneg
  push Not at hneg
  have : Real.jacobiThetaThreeNullQ q * Real.jacobiThetaFourNullQ q < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hneg
  nlinarith [sq_nonneg (Real.jacobiThetaFourNullQ (q ^ 2))]

/-- The nomes `q^{2^n}` tend to `0` from the right. -/
theorem tendsto_pow_two_pow {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => q ^ 2 ^ n) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => pow_pos hq0 _⟩
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

/-- `q^{2^{n+1}} = (q^{2ⁿ})²`. -/
theorem pow_two_pow_succ (q : ℝ) (n : ℕ) : q ^ 2 ^ (n + 1) = (q ^ 2 ^ n) ^ 2 := by
  rw [pow_succ, pow_mul]

/-- `θ₄(q) > 0`: a zero would propagate to `θ₄(q^{2ⁿ}) → 1`. -/
theorem Real.jacobiThetaFourNullQ_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < Real.jacobiThetaFourNullQ q := by
  rcases (Real.jacobiThetaFourNullQ_nonneg hq0 hq1).lt_or_eq with h | h
  · exact h
  exfalso
  have hall : ∀ n : ℕ, Real.jacobiThetaFourNullQ (q ^ 2 ^ n) = 0 := by
    intro n
    induction n with
    | zero => simpa using h.symm
    | succ n ih =>
      have hr0 : 0 < q ^ 2 ^ n := pow_pos hq0 _
      have hr1 : q ^ 2 ^ n < 1 := pow_lt_one₀ hq0.le hq1 (by positivity)
      have := Real.jacobiThetaThreeNullQ_mul_jacobiThetaFourNullQ hr0 hr1
      rw [ih, mul_zero, ← pow_two_pow_succ] at this
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this.symm
  have hlim := Real.tendsto_jacobiThetaFourNullQ.comp (tendsto_pow_two_pow hq0 hq1)
  have h0 : Tendsto (fun n : ℕ => Real.jacobiThetaFourNullQ (q ^ 2 ^ n)) atTop (𝓝 0) := by
    simp only [hall]; exact tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique hlim h0)

/-- `M(θ₃(q)², θ₄(q)²) = 1`: the pairs `(θ₃(q^{2ⁿ})², θ₄(q^{2ⁿ})²)` form the AGM iteration and
tend to `(1, 1)`. -/
theorem Real.agm_jacobiThetaThreeNullQ_sq_jacobiThetaFourNullQ_sq {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) :
    NNReal.agm (Real.jacobiThetaThreeNullQ q ^ 2).toNNReal
        (Real.jacobiThetaFourNullQ q ^ 2).toNNReal = 1 := by
  set X : ℕ → NNReal := fun n => (Real.jacobiThetaThreeNullQ (q ^ 2 ^ n) ^ 2).toNNReal with hX
  set Y : ℕ → NNReal := fun n => (Real.jacobiThetaFourNullQ (q ^ 2 ^ n) ^ 2).toNNReal with hY
  have hr0 (n : ℕ) : 0 < q ^ 2 ^ n := pow_pos hq0 _
  have hr1 (n : ℕ) : q ^ 2 ^ n < 1 := pow_lt_one₀ hq0.le hq1 (by positivity)
  have hstep (n : ℕ) : NNReal.agm (X n) (Y n) = NNReal.agm (X (n + 1)) (Y (n + 1)) := by
    rw [NNReal.agm_eq_agm_gm_am, NNReal.agm_comm]
    have h3 := Real.one_le_jacobiThetaThreeNullQ (hr0 n) (hr1 n)
    have h4 := Real.jacobiThetaFourNullQ_nonneg (hr0 n) (hr1 n)
    congr 1
    · apply NNReal.eq
      simp only [hX, hY, Real.coe_toNNReal _ (sq_nonneg _), NNReal.coe_div,
        NNReal.coe_add, NNReal.coe_ofNat]
      rw [pow_two_pow_succ]
      have := Real.jacobiThetaThreeNullQ_sq_add_jacobiThetaFourNullQ_sq (hr0 n) (hr1 n)
      linarith
    · apply NNReal.eq
      rw [Real.coe_sqrt, NNReal.coe_mul]
      simp only [hX, hY, Real.coe_toNNReal _ (sq_nonneg _)]
      rw [pow_two_pow_succ, ← Real.jacobiThetaThreeNullQ_mul_jacobiThetaFourNullQ (hr0 n) (hr1 n),
        show Real.jacobiThetaThreeNullQ (q ^ 2 ^ n) ^ 2 *
            Real.jacobiThetaFourNullQ (q ^ 2 ^ n) ^ 2 =
          (Real.jacobiThetaThreeNullQ (q ^ 2 ^ n) * Real.jacobiThetaFourNullQ (q ^ 2 ^ n)) ^ 2 by
          ring,
        Real.sqrt_sq (mul_nonneg (by linarith) h4)]
  have hconst (n : ℕ) : NNReal.agm (X 0) (Y 0) = NNReal.agm (X n) (Y n) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [ih, hstep]
  have hXl : Tendsto X atTop (𝓝 1) := by
    have h := (continuous_real_toNNReal.tendsto _).comp
      ((Real.tendsto_jacobiThetaThreeNullQ.comp (tendsto_pow_two_pow hq0 hq1)).pow 2)
    simp only [one_pow, Real.toNNReal_one] at h
    exact h
  have hYl : Tendsto Y atTop (𝓝 1) := by
    have h := (continuous_real_toNNReal.tendsto _).comp
      ((Real.tendsto_jacobiThetaFourNullQ.comp (tendsto_pow_two_pow hq0 hq1)).pow 2)
    simp only [one_pow, Real.toNNReal_one] at h
    exact h
  have h0 : NNReal.agm (Real.jacobiThetaThreeNullQ q ^ 2).toNNReal
      (Real.jacobiThetaFourNullQ q ^ 2).toNNReal =
      NNReal.agm (X 0) (Y 0) := by simp [hX, hY]
  rw [h0]
  apply le_antisymm
  · have hmax := hXl.max hYl
    rw [max_self] at hmax
    exact ge_of_tendsto' hmax fun n => (hconst n) ▸ NNReal.agm_le_max
  · have hmin := hXl.min hYl
    rw [min_self] at hmin
    exact le_of_tendsto' hmin fun n => (hconst n) ▸ NNReal.min_le_agm

/-- **Jacobi's formula** `K = (π/2) θ₃²` (DLMF 20.9.2) for a real nome `0 < q < 1`, with the
complementary modulus `k' = θ₄(q)²/θ₃(q)²`, i.e. `m = 1 - θ₄⁴/θ₃⁴`. The proof combines the
theta doubling identities, which make `(θ₃(q^{2ⁿ})², θ₄(q^{2ⁿ})²)` an AGM sequence, with Gauss's
theorem `K(m) = π/(2 M(1, √(1-m)))`. -/
@[dlmf 20.9.E2]
theorem Real.compEllIntKm_eq_jacobiThetaThreeNullQ {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Real.compEllIntKm (1 - (Real.jacobiThetaFourNullQ q / Real.jacobiThetaThreeNullQ q) ^ 4) =
      π / 2 * Real.jacobiThetaThreeNullQ q ^ 2 := by
  set a := Real.jacobiThetaThreeNullQ q
  set b := Real.jacobiThetaFourNullQ q
  have ha : 0 < a := lt_of_lt_of_le one_pos (Real.one_le_jacobiThetaThreeNullQ hq0 hq1)
  have hb : 0 < b := Real.jacobiThetaFourNullQ_pos hq0 hq1
  set kp := (b / a) ^ 2 with hkp
  have hkp0 : 0 < kp := by positivity
  have hm : 1 - (b / a) ^ 4 < 1 := by
    have : 0 < (b / a) ^ 4 := by positivity
    linarith
  rw [Real.compEllIntKm_eq_pi_div_agm hm]
  have hsq : NNReal.sqrt (1 - (1 - (b / a) ^ 4)).toNNReal = kp.toNNReal := by
    apply NNReal.eq
    rw [Real.coe_sqrt, Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ hkp0.le,
      show 1 - (1 - (b / a) ^ 4) = kp ^ 2 by rw [hkp]; ring, Real.sqrt_sq hkp0.le]
  rw [hsq]
  have hagm := Real.agm_jacobiThetaThreeNullQ_sq_jacobiThetaFourNullQ_sq hq0 hq1
  have hdist := NNReal.agm_mul_distrib (k := (a ^ 2).toNNReal) (x := 1) (y := kp.toNNReal)
  rw [mul_one, ← Real.toNNReal_mul (by positivity),
    show a ^ 2 * kp = b ^ 2 by rw [hkp]; field_simp, hagm] at hdist
  have hval : (NNReal.agm 1 kp.toNNReal : ℝ) = 1 / a ^ 2 := by
    have h := congrArg (fun x : NNReal => (x : ℝ)) hdist
    simp only [NNReal.coe_one, NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg a)] at h
    field_simp
    linarith
  rw [hval]
  field_simp

/-- On the imaginary axis `τ = it` the DLMF theta functions are the real series in the nome
`q = e^{-πt}`: `θ₃(0|it) = θ₃(e^{-πt})`. -/
theorem jacobiThetaThreeTau_zero_I_mul (t : ℝ) :
    jacobiThetaThreeTau 0 (Complex.I * t) = Real.jacobiThetaThreeNullQ (exp (-(π * t))) := by
  rw [jacobiThetaThreeTau_eq_tsum, Real.jacobiThetaThreeNullQ, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_zpow, Complex.ofReal_exp, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `θ₄(0|it) = θ₄(e^{-πt})`. -/
theorem jacobiThetaFourTau_zero_I_mul (t : ℝ) :
    jacobiThetaFourTau 0 (Complex.I * t) = Real.jacobiThetaFourNullQ (exp (-(π * t))) := by
  rw [jacobiThetaFourTau_eq_tsum, Real.jacobiThetaFourNullQ, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_zpow, Complex.ofReal_exp,
    ← Complex.exp_int_mul]
  push_cast
  congr 2
  ring_nf
  rw [Complex.I_sq]
  ring

end DLMF.Elliptic

end
