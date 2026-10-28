# DLMF Chapter 2 acquisition: Asymptotic Approximations

This acquisition covers the definitions, numbered formulas and analytical assertions in prose
of [DLMF Chapter 2](https://dlmf.nist.gov/2), version 1.2.8, checked on 2026-10-27, by two
agents working in parallel: g2a (§§2.1–2.5) and g2b (§§2.6–2.11). Helper lemmas carry the
agent's prefix (`g2a_`, `g2b_`) or are private. The Lean code is in
`DLMF/AsymptoticApproximations/` (namespace `DLMF.AsymptoticApproximations`), with one
subdirectory per section group, each with its own `Defs` file. Expansions use the project API
`HasAsymptoticExpansion` of `DLMFMathlib/Analysis/Asymptotics`; Watson's lemma, Euler–Maclaurin
and Liouville–Green material of `DLMFMathlib` is reused. The umbrella is
[DLMF/AsymptoticApproximations.lean](DLMF/AsymptoticApproximations.lean). The parts below are
the agents' ledgers, assembled unchanged apart from heading levels.

**Admissions at acquisition** (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`):
136 in all. By subdirectory: Basics 13, Integrals 22, Mellin 18, Distributional 25, ODE 27,
Sums 24, Remainders 7.

**Source corrections found in this acquisition** (details in the parts; the confirmed errata
are also in `reports/DLMFErrata.tex`): 2.5.11, 2.5.15, 2.5.16 (sign of the residue sum, and the
sum starts at s = 1), §2.10(iv) (2.10.34–2.10.36 need α ∈ (0, π), not (0, 2π)). Convention
notes: 2.3.26 (a(α) carries the sign of α), 2.5.10 at z = 0 (stated in a form without the
removable 0·∞).

## Part g2a: §§2.1–2.5

This part of the Chapter 2 acquisition covers the definitions, numbered formulas and analytical
assertions in prose of [DLMF §§2.1–2.5](https://dlmf.nist.gov/2.1), version 1.2.8, checked on
2026-10-27, by agent g2a (helper prefix `g2a_`). Part g2b covers §§2.6–2.11. The Lean code is in
`DLMF/AsymptoticApproximations/{Basics,Integrals,Mellin}/` (namespace
`DLMF.AsymptoticApproximations`). Expansions use DLMFMathlib's
`Asymptotics.HasAsymptoticExpansion` (scale `φ`, coefficients `a`); nothing depends on part
g2b's files.

Modules, in import order:

- §§2.1–2.2: [Basics/Defs](DLMF/AsymptoticApproximations/Basics/Defs.lean) (Mathlib and
  `DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion`) →
  [Basics/OrderSymbols](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean) (§2.1; also
  `DLMFMathlib` `AsymptoticInversion`, `WatsonSector`),
  [Basics/Transcendental](DLMF/AsymptoticApproximations/Basics/Transcendental.lean) (§2.2).
- §§2.3–2.4: [Integrals/Defs](DLMF/AsymptoticApproximations/Integrals/Defs.lean) (Mathlib only) →
  [Integrals/Watson](DLMF/AsymptoticApproximations/Integrals/Watson.lean) (§2.3(ii), §2.4(i)–(ii);
  also the definitions file `DLMF.AlgebraicAnalytic.Transforms.Defs` and `DLMFMathlib` Watson
  files) → [Integrals/Parts](DLMF/AsymptoticApproximations/Integrals/Parts.lean) (§2.3(i); also
  `Basics.Defs`); [Integrals/Laplace](DLMF/AsymptoticApproximations/Integrals/Laplace.lean)
  (§2.3(iii), §2.4(iii)–(iv)),
  [Integrals/StationaryPhase](DLMF/AsymptoticApproximations/Integrals/StationaryPhase.lean)
  (§2.3(iv)), [Integrals/Coalescing](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean)
  (§2.3(v), §2.4(v)), each importing `Integrals.Defs`.
- §2.5: [Mellin/Defs](DLMF/AsymptoticApproximations/Mellin/Defs.lean) (Mathlib only) →
  [Mellin/Transforms](DLMF/AsymptoticApproximations/Mellin/Transforms.lean) (§2.5(i)–(ii); also
  the definitions file `DLMF.AlgebraicAnalytic.Complex.Defs` for `residueAt`) →
  [Mellin/SmallParameter](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean) (§2.5(iii);
  also `DLMF.AlgebraicAnalytic.Transforms.Defs`, `DLMF.ExpIntegrals.Expansions`);
  [Mellin/BesselExample](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean) (2.5.8–2.5.16;
  `Mellin.Defs`, `DLMF.AlgebraicAnalytic.Complex.Defs`, `DLMF.Gamma.MellinBarnes`,
  `DLMF.Gamma.Asymptotics`).
- [Basics/MathlibCoverage](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean):
  `dlmf_upstream` pointers (`DLMF.Core.Upstream`, Mathlib, DLMFMathlib, lean-codes `ToMathlib`,
  `DLMF.AlgebraicAnalytic.Transforms.Defs`).

All definitions are in the three `Defs` files. No umbrella file is edited; the coordinator adds
the modules to `DLMF.lean`.

**Counts.** §§2.1–2.5 have 132 numbered equations (2.1: 21, 2.2: 8, 2.3: 33, 2.4: 21,
2.5: 49) and 2 tables (2.5.T1, 2.5.T2): 134 IDs in scope. Covered: 132; 2 are no statement
(notation: 2.4.17, 2.5.32). No item is excluded as numerical. Of the 132, 56 carry a proved
theorem, 61 admitted theorems only, 9 definitions only and 6 upstream pointers only. In
addition 17 prose IDs (sections and subsections) carry tags or pointers. 149 DLMF IDs are
tagged or pointed to, on 130 tagged declarations and 24 `dlmf_upstream` pointers. The 157 declarations are
25 definitions (16 tagged, 9 untagged helper definitions), 79 proved theorems (18 untagged
helpers) and 53 admitted theorems. Four proved theorems depend on admissions
(`mellin_convolution_eq_mellinInv` and `laplace_trunc_eq_mellinInv` on 2.5.4,
`mellin_besselJ_sq_eq_kernel` on 2.5.10, `besselSq_integral_expansion_odd` on 2.5.15); the
other 67 public proved theorems use only `propext`, `Classical.choice`, `Quot.sound`.

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`):

- [Basics/Defs](DLMF/AsymptoticApproximations/Basics/Defs.lean): 0; 8 definitions.
- [Basics/OrderSymbols](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean): 9; 33 theorems:
  24 proved, 9 admitted.
- [Basics/Transcendental](DLMF/AsymptoticApproximations/Basics/Transcendental.lean): 4;
  9 theorems: 5 proved, 4 admitted.
- [Integrals/Defs](DLMF/AsymptoticApproximations/Integrals/Defs.lean): 0; 12 definitions.
- [Integrals/Watson](DLMF/AsymptoticApproximations/Integrals/Watson.lean): 7; 14 theorems:
  7 proved, 7 admitted.
- [Integrals/Parts](DLMF/AsymptoticApproximations/Integrals/Parts.lean): 4; 5 theorems: 1 proved,
  4 admitted.
- [Integrals/Laplace](DLMF/AsymptoticApproximations/Integrals/Laplace.lean): 5; 14 theorems:
  9 proved, 5 admitted.
- [Integrals/StationaryPhase](DLMF/AsymptoticApproximations/Integrals/StationaryPhase.lean): 3;
  3 theorems admitted.
- [Integrals/Coalescing](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean): 3;
  9 theorems: 6 proved, 3 admitted.
- [Mellin/Defs](DLMF/AsymptoticApproximations/Mellin/Defs.lean): 0; 5 definitions.
- [Mellin/Transforms](DLMF/AsymptoticApproximations/Mellin/Transforms.lean): 5; 16 theorems:
  11 proved, 5 admitted.
- [Mellin/BesselExample](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean): 5;
  14 theorems: 9 proved, 5 admitted.
- [Mellin/SmallParameter](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean): 8;
  15 theorems: 7 proved, 8 admitted.
- [Basics/MathlibCoverage](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean): 0;
  24 `dlmf_upstream` pointers.

Total: 53 admissions.

### Domains, conventions and source corrections (part g2a)

- **Order symbols and expansions.** Mathlib's `~[l]`, `=o[l]`, `=O[l]` are used for 2.1.1–2.1.3
  (pointers record the equivalence with DLMF's quotient forms when the comparison function is
  eventually nonzero). A Poincaré expansion `f(x) ∼ ∑ aₛ x^{-s}` as `x → ∞` in a set `X`
  (2.1.13–2.1.14) is `HasPoincareExpansion X a f`, the DLMFMathlib expansion on the filter
  `cobounded 𝕜 ⊓ 𝓟 X` with scale `x⁻¹ˢ`; at a finite point `c` it is
  `HasPoincareExpansionAt` (2.1.16); uniform expansions (2.1.18) use the product filter
  `𝓟 U ×ˢ (cobounded ⊓ 𝓟 X)`; generalized expansions (2.1.19–2.1.21) are
  `HasGeneralizedAsymptoticExpansion l φ fs f` (asymptotic scale plus remainders). Where DLMF
  writes two series that are "interpreted separately" (§2.1(iii)), the statement gives the
  remainder after `N` and `M` terms as a sum of two `O`-terms.
- **Infinitely differentiable.** `ContDiffOn ℝ ∞` (`open scoped ContDiff`; `⊤` would mean
  analytic). Derivatives at endpoints are one-sided (`iteratedDerivWithin` on the closed
  interval); "infinitely differentiable expansions" are the expansions of all derivatives with
  termwise differentiated coefficients (`descPochhammer`).
- **Improper and uniformly convergent integrals.** Integrals that DLMF requires to converge
  uniformly for large `x` are limits `lim_{T→∞} ∫^T` with `TendstoUniformlyOn` hypotheses.
- **Watson's lemma.** The general-exponent version used for 2.3.7–2.3.8 and 2.3.2
  (`hasAsymptoticExpansion_integral_exp_smul_rpow_seq`, untagged) is adapted from DLMFMathlib's
  `hasAsymptoticExpansion_integral_exp_smul` (one exponent shift `μ`) and is new, not a copy;
  the sector version 2.4.1 rests on DLMFMathlib's
  `hasAsymptoticExpansion_integral_cexp_smul_sector`.
- **Laplace coefficients.** `laplaceCoeff L₀ p q λ μ s` is 2.3.18 with `p₀^{α}` written
  `exp(α L₀)` (`exp L₀ = p₀`), so that complex `p₀` (2.4.13) is covered with an explicit branch.
- **Bleistein's method (2.3.26), sign correction.** DLMF prints `a = (2p(α,0) - 2p(α,α))^{1/2}`;
  for `α < 0` this does not give `w(0) = 0` under 2.3.27, which DLMF requires. `bleisteinA`
  carries the sign of `α`; `bleisteinW_zero` and `bleisteinW_self` are proved.
- **Mellin transforms.** `mellin` and `mellinInv` are Mathlib's; `mellinInv σ F x` is
  `(2πi)⁻¹ ∫_{σ-i∞}^{σ+i∞} x^{-z} F(z) dz`. Residues are `DLMF.AlgebraicAnalytic.residueAt`
  (circle integrals, §1.10(iii)). Contour shifts are stated for a finite set of poles in the
  strip, decay uniform in the strip (2.5.34) and integrability along both lines. The
  continuations 2.5.25–2.5.28 are existence statements (`∃ F`, analytic after removal of the
  principal parts `∑_{s<N}`), and in 2.5.43–2.5.44 the continuation `H` of `𝓜h₂` is a
  hypothesis with these properties.
- **Reciprocal Gamma.** `(Complex.Gamma w)⁻¹` is the entire `1/Γ`, since Mathlib's `Γ` is `0` at
  the poles; the printed form of 2.5.10 is `0·∞` at `z = 0` and is therefore stated in the
  equivalent form with `Γ(1 - z)`.
- **Erratum 2.5.11 / 2.5.15 / 2.5.16 (signs).** The residue in 2.5.11 is
  `-(aₙ ln x + bₙ)x^{-n}` (with `bₙ = -A′(n)`, `A` the factor in 2.5.10), so that
  `I(x) = +∑_{s=1}^{2n}(aₛ ln x + bₛ)x^{-s} + O(x^{-2n-1+ε})` and `cₛ = a_{2s+1}`,
  `dₛ = b_{2s+1}` in 2.5.16. Numerical check (mpmath, scratch script
  `g2a_check2515.py`): `ν = 0`, `x = 20`: `I = 0.0899450`, `(ln 20 + 3 ln 2 + γ)/(20π) =
  0.0899606`; the same agreement for `ν = 0.3` and `x = 10`. Also, `b₀ = -A′(0)` is not `0` (DLMF's
  claim `a_s = b_s = 0` for even `s` holds for `s ≥ 2`), and the `s = 0` term is outside the strip
  crossed by the contour, so the sum in 2.5.15 starts at `s = 1`.
- **2.5.13.** `besselSqMellinB` is `-A′(n)`, which agrees with DLMF's digamma expression when
  all Gamma factors of `aₙ` are finite and nonzero and also covers the degenerate cases.
- **Real parameters in §2.5(iii).** `ζ > 0` real throughout except 2.5.49 for `ℜζ > 0`
  (admitted); 2.5.48 is proved in convergent form for `ζ > 0`.

### Numbered formulas and prose items (part g2a)

## [§2.1 Definitions and Elementary Properties](https://dlmf.nist.gov/2.1)

- [2.1.E1](https://dlmf.nist.gov/2.1.E1): upstream [`Asymptotics.isEquivalent_iff_tendsto_one`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L36) (different convention: f ~ g iff f/g → 1, when g is eventually nonzero). Mathlib `f ~[l] g` is `f - g = o(g)`; equivalent to `f/g → 1` when `g` is eventually nonzero.
- [2.1.E2](https://dlmf.nist.gov/2.1.E2): upstream [`Asymptotics.isLittleO_iff_tendsto'`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L38) (different convention: f = o(g) iff f/g → 0, when g x = 0 → f x = 0 eventually).
- [2.1.E3](https://dlmf.nist.gov/2.1.E3): upstream [`Asymptotics.isBigO_iff_isBoundedUnder_le_div`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L40) (different convention: f = O(g) iff |f/g| is bounded, when g is eventually nonzero).
- [2.1.E4](https://dlmf.nist.gov/2.1.E4): [`DLMF.AsymptoticApproximations.tanh_isEquivalent_id`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L35) (proved).
- [2.1.E5](https://dlmf.nist.gov/2.1.E5): [`DLMF.AsymptoticApproximations.exp_neg_isLittleO_one`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L50) (proved).
- [2.1.E6](https://dlmf.nist.gov/2.1.E6): [`DLMF.AsymptoticApproximations.sin_pi_mul_add_inv_isBigO`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L95) (proved).
- [2.1.E7](https://dlmf.nist.gov/2.1.E7): [`DLMF.AsymptoticApproximations.cexp_mul_I_isBigO_one`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L107) (proved).
- [2.1.E8](https://dlmf.nist.gov/2.1.E8): [`DLMF.AsymptoticApproximations.tsum_tail_isBigO_pow`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L114) (proved); upstream [`HasFPowerSeriesAt.isBigO_sub_partialSum_pow`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L52) (stronger: a convergent power series is an asymptotic expansion, f - partial sum = O(zⁿ)). Proved for a power series convergent in a disc: the tail after `n` terms is `O(zⁿ)`.
- [2.1.E9](https://dlmf.nist.gov/2.1.E9): [`DLMF.AsymptoticApproximations.cexp_sub_one_sub_isBigO_sq`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L157) (proved).
- [2.1.E10](https://dlmf.nist.gov/2.1.E10): upstream [`Asymptotics.IsLittleO.isBigO`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L44) (exact: o(φ) is O(φ)); upstream [`Asymptotics.IsBigO.add`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L46) (exact: O(φ) + O(φ) = O(φ)); upstream [`Asymptotics.IsLittleO.add`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L48) (exact: o(φ) + o(φ) = o(φ)).
- [2.1.E11](https://dlmf.nist.gov/2.1.E11): [`DLMF.AsymptoticApproximations.integral_Ioi_isEquivalent_of_isEquivalent_cpow`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L168) (admitted). Integrated relation for `f ∼ x^ν`, `ℜν < -1`, complex `ν`.
- [2.1.E12](https://dlmf.nist.gov/2.1.E12): [`DLMF.AsymptoticApproximations.exists_tendsto_intervalIntegral_of_isEquivalent_cpow`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L178) (admitted); [`DLMF.AsymptoticApproximations.intervalIntegral_isEquivalent_log`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L187) (admitted); [`DLMF.AsymptoticApproximations.intervalIntegral_isEquivalent_cpow`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L195) (admitted). Three statements: convergence/divergence of the integral and the equivalents `ln x` (`ν = -1`) and `x^{ν+1}/(ν+1)` (`ℜν > -1`).
- [2.1.E13](https://dlmf.nist.gov/2.1.E13): [`DLMF.AsymptoticApproximations.HasPoincareExpansion`](DLMF/AsymptoticApproximations/Basics/Defs.lean#L42) (definition).
- [2.1.E14](https://dlmf.nist.gov/2.1.E14): [`DLMF.AsymptoticApproximations.HasPoincareExpansion`](DLMF/AsymptoticApproximations/Basics/Defs.lean#L42) (definition).
- [2.1.E15](https://dlmf.nist.gov/2.1.E15): [`DLMF.AsymptoticApproximations.hasPoincareExpansion_iff_tendsto`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L243) (proved).
- [2.1.E16](https://dlmf.nist.gov/2.1.E16): [`DLMF.AsymptoticApproximations.HasPoincareExpansionAt`](DLMF/AsymptoticApproximations/Basics/Defs.lean#L52) (definition).
- [2.1.E17](https://dlmf.nist.gov/2.1.E17): [`DLMF.AsymptoticApproximations.hasPoincareExpansion_zero`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L392) (proved); [`DLMF.AsymptoticApproximations.hasPoincareExpansion_cexp_neg`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L399) (proved); [`DLMF.AsymptoticApproximations.hasPoincareExpansion_cexp_neg_sqrt`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L431) (admitted). Expansion of `e^{-x}` (all coefficients `0`, proved) and of `e^{-√x}`-type examples (admitted); illustrates non-uniqueness of the function.
- [2.1.E18](https://dlmf.nist.gov/2.1.E18): [`DLMF.AsymptoticApproximations.HasUniformPoincareExpansion`](DLMF/AsymptoticApproximations/Basics/Defs.lean#L59) (definition); [`DLMF.AsymptoticApproximations.hasUniformPoincareExpansion_iff`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L450) (admitted). `HasUniformPoincareExpansion` uses the product filter `𝓟 U ×ˢ (cobounded ⊓ 𝓟 X)`.
- [2.1.E19](https://dlmf.nist.gov/2.1.E19): [`DLMF.AsymptoticApproximations.HasGeneralizedAsymptoticExpansion`](DLMF/AsymptoticApproximations/Basics/Defs.lean#L69) (definition); upstream [`Asymptotics.IsAsymptoticScale`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L58) (exact: φ_{s+1} = o(φ_s) (DLMFMathlib)).
- [2.1.E20](https://dlmf.nist.gov/2.1.E20): [`DLMF.AsymptoticApproximations.HasGeneralizedAsymptoticExpansion`](DLMF/AsymptoticApproximations/Basics/Defs.lean#L69) (definition); upstream [`Asymptotics.HasAsymptoticExpansion`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L60) (special case: ∑ aₛ φₛ with constant aₛ (DLMFMathlib); see HasGeneralizedAsymptoticExpansion).
- [2.1.E21](https://dlmf.nist.gov/2.1.E21): [`DLMF.AsymptoticApproximations.HasGeneralizedAsymptoticExpansion`](DLMF/AsymptoticApproximations/Basics/Defs.lean#L69) (definition).

## [§2.2 Transcendental Equations](https://dlmf.nist.gov/2.2)

- [2.2.E1](https://dlmf.nist.gov/2.2.E1): [`DLMF.AsymptoticApproximations.existsUnique_root_of_isEquivalent`](DLMF/AsymptoticApproximations/Basics/Transcendental.lean#L30) (proved).
- [2.2.E2](https://dlmf.nist.gov/2.2.E2): [`DLMF.AsymptoticApproximations.root_isEquivalent`](DLMF/AsymptoticApproximations/Basics/Transcendental.lean#L46) (proved).
- [2.2.E3](https://dlmf.nist.gov/2.2.E3): [`DLMF.AsymptoticApproximations.existsUnique_sq_sub_log_eq`](DLMF/AsymptoticApproximations/Basics/Transcendental.lean#L88) (proved).
- [2.2.E4](https://dlmf.nist.gov/2.2.E4): [`DLMF.AsymptoticApproximations.sq_sub_log_root_isEquivalent`](DLMF/AsymptoticApproximations/Basics/Transcendental.lean#L116) (admitted).
- [2.2.E5](https://dlmf.nist.gov/2.2.E5): [`DLMF.AsymptoticApproximations.sq_sub_log_root_sq`](DLMF/AsymptoticApproximations/Basics/Transcendental.lean#L124) (admitted).
- [2.2.E6](https://dlmf.nist.gov/2.2.E6): [`DLMF.AsymptoticApproximations.sq_sub_log_root_second`](DLMF/AsymptoticApproximations/Basics/Transcendental.lean#L132) (admitted).
- [2.2.E7](https://dlmf.nist.gov/2.2.E7): [`DLMF.AsymptoticApproximations.lagrange_reversion`](DLMF/AsymptoticApproximations/Basics/Transcendental.lean#L140) (admitted).
- [2.2.E8](https://dlmf.nist.gov/2.2.E8): [`DLMF.AsymptoticApproximations.lagrangeReversionCoeff`](DLMF/AsymptoticApproximations/Basics/Defs.lean#L78) (definition); [`DLMF.AsymptoticApproximations.lagrange_reversion`](DLMF/AsymptoticApproximations/Basics/Transcendental.lean#L140) (admitted). Lagrange coefficients via `PowerSeries.coeff`; checked with sympy against the series reversion (F₁ = f₁, F₂ = f₀f₁ + f₂, …).

## [§2.3 Integrals of a Real Variable](https://dlmf.nist.gov/2.3)

- [2.3.E1](https://dlmf.nist.gov/2.3.E1): upstream [`DLMF.AlgebraicAnalytic.laplaceTransform`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L68) (exact: the Laplace transform of §1.14 (DLMF 1.14.17)); [`DLMF.AsymptoticApproximations.watson_lemma`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L89) (proved); [`DLMF.AsymptoticApproximations.watson_lemma_laplaceTransform`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L108) (proved).
- [2.3.E2](https://dlmf.nist.gov/2.3.E2): [`DLMF.AsymptoticApproximations.laplace_hasAsymptoticExpansion_of_contDiffOn`](DLMF/AsymptoticApproximations/Integrals/Parts.lean#L36) (proved).
- [2.3.E3](https://dlmf.nist.gov/2.3.E3): [`DLMF.AsymptoticApproximations.laplace_error_bound`](DLMF/AsymptoticApproximations/Integrals/Parts.lean#L79) (admitted).
- [2.3.E4](https://dlmf.nist.gov/2.3.E4): [`DLMF.AsymptoticApproximations.fourier_hasGeneralizedAsymptoticExpansion`](DLMF/AsymptoticApproximations/Integrals/Parts.lean#L94) (admitted); [`DLMF.AsymptoticApproximations.fourier_error_bound`](DLMF/AsymptoticApproximations/Integrals/Parts.lean#L107) (admitted).
- [2.3.E5](https://dlmf.nist.gov/2.3.E5): [`DLMF.AsymptoticApproximations.fourier_Ioi_hasGeneralizedAsymptoticExpansion`](DLMF/AsymptoticApproximations/Integrals/Parts.lean#L119) (admitted).
- [2.3.E6](https://dlmf.nist.gov/2.3.E6): upstream [`eVariationOn`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L90) (different convention: total variation as an extended real; 𝒱 of 2.3.6 is variationalOperator); [`DLMF.AsymptoticApproximations.variationalOperator`](DLMF/AsymptoticApproximations/Integrals/Defs.lean#L36) (definition); [`DLMF.AsymptoticApproximations.fourier_error_bound`](DLMF/AsymptoticApproximations/Integrals/Parts.lean#L107) (admitted). `variationalOperator a b f` is `∫ₐᵇ |f′|` for differentiable `f` (DLMF 2.3.6); Mathlib `eVariationOn` (pointer) is the total variation in `ℝ≥0∞`.
- [2.3.E7](https://dlmf.nist.gov/2.3.E7): [`DLMF.AsymptoticApproximations.watson_lemma`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L89) (proved).
- [2.3.E8](https://dlmf.nist.gov/2.3.E8): upstream [`hasAsymptoticExpansion_integral_exp_smul`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L70) (special case: Watson's lemma 2.3.8 with DLMF's μ = 1 (DLMFMathlib's μ is DLMF's λ)); upstream [`hasAsymptoticExpansion_integral_exp_smul_cpow`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L72) (stronger: Watson's lemma with complex exponent μ, ℜμ > 0 (DLMFMathlib)); [`DLMF.AsymptoticApproximations.watson_lemma`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L89) (proved); [`DLMF.AsymptoticApproximations.watson_lemma_laplaceTransform`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L108) (proved).
- [2.3.E9](https://dlmf.nist.gov/2.3.E9): [`DLMF.AsymptoticApproximations.watson_lemma_log`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L126) (admitted).
- [2.3.E10](https://dlmf.nist.gov/2.3.E10): [`DLMF.AsymptoticApproximations.watson_lemma_kernel`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L143) (admitted).
- [2.3.E11](https://dlmf.nist.gov/2.3.E11): [`DLMF.AsymptoticApproximations.watson_lemma_kernel`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L143) (admitted).
- [2.3.E12](https://dlmf.nist.gov/2.3.E12): [`DLMF.AsymptoticApproximations.watson_lemma_kernel`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L143) (admitted).
- [2.3.E13](https://dlmf.nist.gov/2.3.E13): [`DLMF.AsymptoticApproximations.laplace_method`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L38) (admitted); [`DLMF.AsymptoticApproximations.laplace_method_Ioi`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L66) (admitted).
- [2.3.E14](https://dlmf.nist.gov/2.3.E14): [`DLMF.AsymptoticApproximations.laplace_method`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L38) (admitted).
- [2.3.E15](https://dlmf.nist.gov/2.3.E15): [`DLMF.AsymptoticApproximations.laplace_method`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L38) (admitted); [`DLMF.AsymptoticApproximations.laplace_method_Ioi`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L66) (admitted). Error estimate checked with mpmath for `p = t² + t³`, `q = 1 + 2t`.
- [2.3.E16](https://dlmf.nist.gov/2.3.E16): [`DLMF.AsymptoticApproximations.laplaceCoeff_hasAsymptoticExpansion`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L87) (admitted).
- [2.3.E17](https://dlmf.nist.gov/2.3.E17): [`DLMF.AsymptoticApproximations.laplaceCoeff_zero`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L122) (proved); [`DLMF.AsymptoticApproximations.laplaceCoeff_one`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L131) (proved); [`DLMF.AsymptoticApproximations.laplaceCoeff_two`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L142) (proved). `b₀, b₁, b₂` from `laplaceCoeff`; checked against 2.3.18 with sympy.
- [2.3.E18](https://dlmf.nist.gov/2.3.E18): [`DLMF.AsymptoticApproximations.laplaceCoeff`](DLMF/AsymptoticApproximations/Integrals/Defs.lean#L55) (definition); [`DLMF.AsymptoticApproximations.laplaceCoeff_hasAsymptoticExpansion`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L87) (admitted).
- [2.3.E19](https://dlmf.nist.gov/2.3.E19): [`DLMF.AsymptoticApproximations.stationaryPhase_endpoint`](DLMF/AsymptoticApproximations/Integrals/StationaryPhase.lean#L59) (admitted).
- [2.3.E20](https://dlmf.nist.gov/2.3.E20): [`DLMF.AsymptoticApproximations.stationaryPhase_watson`](DLMF/AsymptoticApproximations/Integrals/StationaryPhase.lean#L38) (admitted).
- [2.3.E21](https://dlmf.nist.gov/2.3.E21): [`DLMF.AsymptoticApproximations.stationaryPhaseP`](DLMF/AsymptoticApproximations/Integrals/Defs.lean#L72) (definition); [`DLMF.AsymptoticApproximations.stationaryPhase_endpoint`](DLMF/AsymptoticApproximations/Integrals/StationaryPhase.lean#L59) (admitted).
- [2.3.E22](https://dlmf.nist.gov/2.3.E22): [`DLMF.AsymptoticApproximations.stationaryPhase_endpoint_infinite`](DLMF/AsymptoticApproximations/Integrals/StationaryPhase.lean#L90) (admitted).
- [2.3.E23](https://dlmf.nist.gov/2.3.E23): [`DLMF.AsymptoticApproximations.stationaryPhase_endpoint`](DLMF/AsymptoticApproximations/Integrals/StationaryPhase.lean#L59) (admitted); [`DLMF.AsymptoticApproximations.stationaryPhase_endpoint_infinite`](DLMF/AsymptoticApproximations/Integrals/StationaryPhase.lean#L90) (admitted). The two series are interpreted separately (§2.1(iii)); the remainder after `N` and `M` terms is `O(x^{-(N+λ)/μ}) + O(x^{-M-1})`.
- [2.3.E24](https://dlmf.nist.gov/2.3.E24): [`DLMF.AsymptoticApproximations.bleistein_transform`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L110) (admitted).
- [2.3.E25](https://dlmf.nist.gov/2.3.E25): [`DLMF.AsymptoticApproximations.bleistein_quadratic`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L42) (proved).
- [2.3.E26](https://dlmf.nist.gov/2.3.E26): [`DLMF.AsymptoticApproximations.bleisteinA`](DLMF/AsymptoticApproximations/Integrals/Defs.lean#L78) (definition); [`DLMF.AsymptoticApproximations.bleisteinB`](DLMF/AsymptoticApproximations/Integrals/Defs.lean#L86) (definition); [`DLMF.AsymptoticApproximations.bleisteinW_zero`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L54) (proved); [`DLMF.AsymptoticApproximations.bleisteinW_self`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L65) (proved). **Sign correction**: `a(α)` must carry the sign of `α` (`a = sgn(α)·(2p(α,0) - 2p(α,α))^{1/2}`) for `t = 0` to correspond to `w = 0` when `α < 0`, as DLMF requires before 2.3.26; implemented in `bleisteinA`, `bleisteinW_zero` proved.
- [2.3.E27](https://dlmf.nist.gov/2.3.E27): [`DLMF.AsymptoticApproximations.bleisteinW`](DLMF/AsymptoticApproximations/Integrals/Defs.lean#L91) (definition).
- [2.3.E28](https://dlmf.nist.gov/2.3.E28): [`DLMF.AsymptoticApproximations.bleisteinW_hasDerivAt`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L70) (proved).
- [2.3.E29](https://dlmf.nist.gov/2.3.E29): [`DLMF.AsymptoticApproximations.bleistein_transform`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L110) (admitted).
- [2.3.E30](https://dlmf.nist.gov/2.3.E30): [`DLMF.AsymptoticApproximations.bleistein_transform`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L110) (admitted).
- [2.3.E31](https://dlmf.nist.gov/2.3.E31): [`DLMF.AsymptoticApproximations.bleistein_uniform`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L127) (admitted).
- [2.3.E32](https://dlmf.nist.gov/2.3.E32): [`DLMF.AsymptoticApproximations.bleistein_uniform`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L127) (admitted).
- [2.3.E33](https://dlmf.nist.gov/2.3.E33): [`DLMF.AsymptoticApproximations.bleisteinF`](DLMF/AsymptoticApproximations/Integrals/Defs.lean#L99) (definition); [`DLMF.AsymptoticApproximations.bleistein_uniform`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L127) (admitted).

## [§2.4 Contour Integrals](https://dlmf.nist.gov/2.4)

- [2.4.E1](https://dlmf.nist.gov/2.4.E1): upstream [`hasAsymptoticExpansion_integral_cexp_smul_sector`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L74) (exact: Watson's lemma in a sector |ph z| ≤ π/2 - δ (DLMFMathlib)); [`DLMF.AsymptoticApproximations.watson_lemma_sector`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L217) (proved).
- [2.4.E2](https://dlmf.nist.gov/2.4.E2): [`DLMF.AsymptoticApproximations.laplace_inversion`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L274) (admitted).
- [2.4.E3](https://dlmf.nist.gov/2.4.E3): [`DLMF.AsymptoticApproximations.laplace_inversion`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L274) (admitted).
- [2.4.E4](https://dlmf.nist.gov/2.4.E4): [`DLMF.AsymptoticApproximations.inverseLaplace_of_hasAsymptoticExpansion`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L286) (admitted).
- [2.4.E5](https://dlmf.nist.gov/2.4.E5): [`DLMF.AsymptoticApproximations.inverseLaplace_of_hasAsymptoticExpansion`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L286) (admitted).
- [2.4.E6](https://dlmf.nist.gov/2.4.E6): [`DLMF.AsymptoticApproximations.haar_sub`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L308) (proved).
- [2.4.E7](https://dlmf.nist.gov/2.4.E7): [`DLMF.AsymptoticApproximations.haar_sub`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L308) (proved).
- [2.4.E8](https://dlmf.nist.gov/2.4.E8): [`DLMF.AsymptoticApproximations.haar_isLittleO`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L336) (admitted).
- [2.4.E9](https://dlmf.nist.gov/2.4.E9): [`DLMF.AsymptoticApproximations.haar_isLittleO_pow`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L349) (admitted).
- [2.4.E10](https://dlmf.nist.gov/2.4.E10): [`DLMF.AsymptoticApproximations.laplace_method_contour`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L160) (admitted).
- [2.4.E11](https://dlmf.nist.gov/2.4.E11): [`DLMF.AsymptoticApproximations.laplace_method_contour`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L160) (admitted).
- [2.4.E12](https://dlmf.nist.gov/2.4.E12): [`DLMF.AsymptoticApproximations.laplace_method_contour`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L160) (admitted).
- [2.4.E13](https://dlmf.nist.gov/2.4.E13): [`DLMF.AsymptoticApproximations.laplace_method_contour`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L160) (admitted).
- [2.4.E14](https://dlmf.nist.gov/2.4.E14): [`DLMF.AsymptoticApproximations.integral_path_split`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L205) (proved).
- [2.4.E15](https://dlmf.nist.gov/2.4.E15): [`DLMF.AsymptoticApproximations.saddle_point`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L217) (admitted).
- [2.4.E16](https://dlmf.nist.gov/2.4.E16): [`DLMF.AsymptoticApproximations.saddle_coeff_zero`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L253) (proved); [`DLMF.AsymptoticApproximations.saddle_coeff_two`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L264) (proved). `b₀`, `b₂` checked with sympy.
- [2.4.E17](https://dlmf.nist.gov/2.4.E17): no statement (notation: the integral `I(α,z) = ∫_𝒫 e^{-zp(α,t)} q(α,t) dt` of §2.4(v); its cubic change of variable is `cfu_deriv`/`cfu_airy_form`, the uniform approximation is excluded: informal)
- [2.4.E18](https://dlmf.nist.gov/2.4.E18): [`DLMF.AsymptoticApproximations.cfu_deriv`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L156) (proved).
- [2.4.E19](https://dlmf.nist.gov/2.4.E19): [`DLMF.AsymptoticApproximations.cfu_airy_form`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L176) (proved).
- [2.4.E20](https://dlmf.nist.gov/2.4.E20): [`DLMF.AsymptoticApproximations.cfu_deriv`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L156) (proved).
- [2.4.E21](https://dlmf.nist.gov/2.4.E21): [`DLMF.AsymptoticApproximations.cfu_airy_form`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L176) (proved).

## [§2.5 Mellin Transform Methods](https://dlmf.nist.gov/2.5)

- [2.5.E1](https://dlmf.nist.gov/2.5.E1): upstream [`mellin`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L82) (exact: 𝓜f(z) = ∫₀^∞ t^{z-1} f(t) dt). Mathlib `mellin f s = ∫₀^∞ t^{s-1} • f t`, the vertical inversion integral is `mellinInv σ F x`.
- [2.5.E2](https://dlmf.nist.gov/2.5.E2): upstream [`mellinInv_mellin_eq`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L84) (exact: Mellin inversion, (2πi)⁻¹ ∫_{(c)} t^{-z} 𝓜f(z) dz = f(t) at continuity points).
- [2.5.E3](https://dlmf.nist.gov/2.5.E3): [`DLMF.AsymptoticApproximations.mellin_convolution`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L44) (admitted).
- [2.5.E4](https://dlmf.nist.gov/2.5.E4): [`DLMF.AsymptoticApproximations.mellin_convolution`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L44) (admitted).
- [2.5.E5](https://dlmf.nist.gov/2.5.E5): [`DLMF.AsymptoticApproximations.mellin_convolution_eq_mellinInv`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L53) (proved from admissions). Stated with absolute convergence of `𝓜f(1-z)`, `𝓜h(z)` on the line, integrability of the product on the line and continuity of `I` at `x`; proved from Mathlib `mellinInv_mellin_eq` and the convolution theorem 2.5.4 (admitted).
- [2.5.E6](https://dlmf.nist.gov/2.5.E6): [`DLMF.AsymptoticApproximations.mellinInv_shift`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L82) (admitted). Residues are `DLMF.AlgebraicAnalytic.residueAt` (§1.10(iii)); stated for a finite set of poles in the strip and decay (2.5.34) uniform in the strip.
- [2.5.E7](https://dlmf.nist.gov/2.5.E7): [`DLMF.AsymptoticApproximations.mellinInv_shift`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L82) (admitted).
- [2.5.E8](https://dlmf.nist.gov/2.5.E8): [`DLMF.AsymptoticApproximations.besselSq_integral_expansion`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L193) (admitted).
- [2.5.E9](https://dlmf.nist.gov/2.5.E9): [`DLMF.AsymptoticApproximations.mellin_inv_one_add_one_sub`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L47) (proved). From `DLMF.Gamma.mellin_one_add_cpow_neg` (Beta integral 5.12.3) and the reflection formula.
- [2.5.E10](https://dlmf.nist.gov/2.5.E10): [`DLMF.AsymptoticApproximations.mellin_besselJ_sq`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L57) (admitted); [`DLMF.AsymptoticApproximations.mellin_besselJ_sq_eq_kernel`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L69) (proved from admissions). Stated as `2^{z-1}Γ(ν+z/2)Γ(1-z)/(Γ²(1-z/2)Γ(1+ν-z/2))`, valid at `z = 0` where the printed form is `0·∞` in Lean; the printed form is proved from it for `sin(πz) ≠ 0`. Checked with mpmath (`ν = 0.3, z = 0.5, -0.3`; `ν = 1.2, z = 0.2`).
- [2.5.E11](https://dlmf.nist.gov/2.5.E11): [`DLMF.AsymptoticApproximations.residueAt_besselSq`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L89) (admitted). **Erratum (sign)**: the residue is `-(aₙ ln x + bₙ)x^{-n}`, since `π²/sin²(πz) ∼ (z-n)^{-2}` and the residue is `d/dz[x^{-z}A(z)]` at `n`, `bₙ = -A′(n)`. Consequently 2.5.15 and 2.5.16 hold with the opposite sign. mpmath: `ν = 0`, `x = 20`: `I(x) = 0.0899450`, `+(a₁ ln x + b₁)/x = 0.0899606` (also `ν = 0.3`, `x = 10, 20`).
- [2.5.E12](https://dlmf.nist.gov/2.5.E12): [`DLMF.AsymptoticApproximations.besselSqMellinA`](DLMF/AsymptoticApproximations/Mellin/Defs.lean#L49) (definition); [`DLMF.AsymptoticApproximations.besselSqMellinA_two_mul`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L109) (proved).
- [2.5.E13](https://dlmf.nist.gov/2.5.E13): [`DLMF.AsymptoticApproximations.besselSqMellinB`](DLMF/AsymptoticApproximations/Mellin/Defs.lean#L54) (definition); [`DLMF.AsymptoticApproximations.besselSqMellinB_eq_digamma`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L100) (admitted); [`DLMF.AsymptoticApproximations.besselSqMellinB_two_mul`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L125) (proved). `besselSqMellinB ν n = -A′(n)`; DLMF's digamma form is `besselSqMellinB_eq_digamma` (odd `n`, `1 + ν - n/2` not a pole); vanishing for even `n ≥ 2` proved. For `n = 0` DLMF's `0·∞` is not zero (`b₀ = -1/(2ν)`), so the sum in 2.5.15 starts at `s = 1`.
- [2.5.E14](https://dlmf.nist.gov/2.5.E14): [`DLMF.AsymptoticApproximations.norm_Gamma_vertical_atTop`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L162) (proved); [`DLMF.AsymptoticApproximations.norm_Gamma_vertical_atBot`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L170) (proved); [`DLMF.AsymptoticApproximations.norm_Gamma_vertical_uniform`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L184) (admitted). Pointwise forms (`y → ±∞`) proved from DLMF 5.11.9 (`DLMF.Gamma.norm_Gamma_imag_large`) and `Γ(z̄) = conj Γ(z)`; uniform form admitted.
- [2.5.E15](https://dlmf.nist.gov/2.5.E15): [`DLMF.AsymptoticApproximations.besselSq_integral_expansion`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L193) (admitted). **Corrected sign** (see 2.5.E11): `I(x) = +∑_{s=1}^{2n}(aₛ ln x + bₛ)x^{-s} + O(x^{-2n-1+ε})`.
- [2.5.E16](https://dlmf.nist.gov/2.5.E16): [`DLMF.AsymptoticApproximations.besselSq_integral_expansion_odd`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L217) (proved from admissions). **Corrected sign**: `cₛ = a_{2s+1}`, `dₛ = b_{2s+1}`; proved from 2.5.15 (admitted) and the vanishing of even coefficients.
- [2.5.E17](https://dlmf.nist.gov/2.5.E17): [`DLMF.AsymptoticApproximations.mellin_truncLow_continuation`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L233) (admitted). `Re αₛ` strictly increasing to `∞`; scale `t^{αₛ}` with complex `αₛ`.
- [2.5.E18](https://dlmf.nist.gov/2.5.E18): [`DLMF.AsymptoticApproximations.mellin_truncHigh_continuation`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L261) (admitted); [`DLMF.AsymptoticApproximations.mellin_truncHigh_continuation_osc`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L276) (admitted). `κ = 0` (2.5.27) and `κ ≠ 0` (entire continuation) stated separately.
- [2.5.E19](https://dlmf.nist.gov/2.5.E19): [`DLMF.AsymptoticApproximations.mellinConvergent_truncHigh`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L171) (proved).
- [2.5.E20](https://dlmf.nist.gov/2.5.E20): [`DLMF.AsymptoticApproximations.mellinConvergent_trunc_h`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L194) (proved).
- [2.5.E21](https://dlmf.nist.gov/2.5.E21): [`DLMF.AsymptoticApproximations.mellinTruncLow`](DLMF/AsymptoticApproximations/Mellin/Defs.lean#L32) (definition).
- [2.5.E22](https://dlmf.nist.gov/2.5.E22): [`DLMF.AsymptoticApproximations.mellinTruncHigh`](DLMF/AsymptoticApproximations/Mellin/Defs.lean#L38) (definition); [`DLMF.AsymptoticApproximations.mellin_eq_truncLow_add_truncHigh`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L248) (proved).
- [2.5.E23](https://dlmf.nist.gov/2.5.E23): [`DLMF.AsymptoticApproximations.mellinTruncLow`](DLMF/AsymptoticApproximations/Mellin/Defs.lean#L32) (definition).
- [2.5.E24](https://dlmf.nist.gov/2.5.E24): [`DLMF.AsymptoticApproximations.mellinTruncHigh`](DLMF/AsymptoticApproximations/Mellin/Defs.lean#L38) (definition); [`DLMF.AsymptoticApproximations.mellin_eq_truncLow_add_truncHigh`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L248) (proved).
- [2.5.E25](https://dlmf.nist.gov/2.5.E25): [`DLMF.AsymptoticApproximations.mellin_truncLow_continuation`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L233) (admitted).
- [2.5.E26](https://dlmf.nist.gov/2.5.E26): [`DLMF.AsymptoticApproximations.mellin_eq_truncLow_add_truncHigh`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L248) (proved).
- [2.5.E27](https://dlmf.nist.gov/2.5.E27): [`DLMF.AsymptoticApproximations.mellin_truncHigh_continuation`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L261) (admitted).
- [2.5.E28](https://dlmf.nist.gov/2.5.E28): [`DLMF.AsymptoticApproximations.mellin_eq_truncLow_add_truncHigh`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L248) (proved).
- [2.5.E29](https://dlmf.nist.gov/2.5.E29): [`DLMF.AsymptoticApproximations.convolution_eq_sum_trunc`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L289) (proved).
- [2.5.E30](https://dlmf.nist.gov/2.5.E30): [`DLMF.AsymptoticApproximations.convolution_eq_sum_trunc`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L289) (proved).
- [2.5.E31](https://dlmf.nist.gov/2.5.E31): [`DLMF.AsymptoticApproximations.integral_truncHigh_mul_truncLow`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L310) (proved).
- [2.5.E32](https://dlmf.nist.gov/2.5.E32): no statement (notation: `G_{jk}(z) = 𝓜f_j(1-z)𝓜h_k(z)` is written out in `mellinInv_shift` and `mellin_convolution_eq_mellinInv`)
- [2.5.E33](https://dlmf.nist.gov/2.5.E33): [`DLMF.AsymptoticApproximations.mellin_convolution_eq_mellinInv`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L53) (proved from admissions).
- [2.5.E34](https://dlmf.nist.gov/2.5.E34): [`DLMF.AsymptoticApproximations.mellinInv_shift`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L82) (admitted).
- [2.5.E35](https://dlmf.nist.gov/2.5.E35): [`DLMF.AsymptoticApproximations.mellinInv_shift`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L82) (admitted).
- [2.5.E36](https://dlmf.nist.gov/2.5.E36): [`DLMF.AsymptoticApproximations.mellinInv_isLittleO`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L114) (proved). Stronger than DLMF: holds for every `G` (Riemann–Lebesgue lemma, Mathlib `Real.tendsto_integral_exp_smul_cocompact`).
- [2.5.E37](https://dlmf.nist.gov/2.5.E37): [`DLMF.AsymptoticApproximations.laplace_eq_trunc_add`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L40) (proved).
- [2.5.E38](https://dlmf.nist.gov/2.5.E38): [`DLMF.AsymptoticApproximations.laplace_eq_trunc_add`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L40) (proved).
- [2.5.E39](https://dlmf.nist.gov/2.5.E39): [`DLMF.AsymptoticApproximations.laplace_eq_trunc_add`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L40) (proved).
- [2.5.E40](https://dlmf.nist.gov/2.5.E40): [`DLMF.AsymptoticApproximations.laplace_trunc_eq_mellinInv`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L68) (proved from admissions).
- [2.5.E41](https://dlmf.nist.gov/2.5.E41): [`DLMF.AsymptoticApproximations.laplace_truncLow_shift`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L97) (admitted).
- [2.5.E42](https://dlmf.nist.gov/2.5.E42): [`DLMF.AsymptoticApproximations.laplace_truncHigh_shift`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L109) (admitted).
- [2.5.E43](https://dlmf.nist.gov/2.5.E43): [`DLMF.AsymptoticApproximations.laplace_remainder_isBigO`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L153) (proved); [`DLMF.AsymptoticApproximations.laplace_expansion_residues`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L170) (admitted). The equality is admitted; the remainder bound `O(ζ^{l-δ-1})` stated after it is proved for every `G` (`laplace_remainder_isBigO`).
- [2.5.E44](https://dlmf.nist.gov/2.5.E44): [`DLMF.AsymptoticApproximations.laplace_small_parameter`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L198) (admitted).
- [2.5.E45](https://dlmf.nist.gov/2.5.E45): [`DLMF.AsymptoticApproximations.residueAt_laplace_inv_one_add`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L220) (admitted); [`DLMF.AsymptoticApproximations.laplace_inv_one_add_eq`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L242) (proved).
- [2.5.E46](https://dlmf.nist.gov/2.5.E46): [`DLMF.AsymptoticApproximations.residueAt_laplace_inv_one_add`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L220) (admitted). Checked with mpmath (`ζ = 0.3`, `k = 1, 2, 3`, contour integrals).
- [2.5.E47](https://dlmf.nist.gov/2.5.E47): [`DLMF.AsymptoticApproximations.residueAt_laplace_inv_one_add_truncHigh`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L230) (admitted). Checked with mpmath (`ζ = 0.3`).
- [2.5.E48](https://dlmf.nist.gov/2.5.E48): [`DLMF.AsymptoticApproximations.hasSum_laplace_inv_one_add`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L273) (proved); [`DLMF.AsymptoticApproximations.laplace_inv_one_add_isBigO`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L293) (admitted). Convergent form proved for `ζ > 0` (stronger than DLMF) from 2.5.49 and DLMF 6.6.3 (`DLMF.Confluent.expIntE1_digamma_series`); the `O(ζᴺ(1 + |ln ζ|))` form admitted. Checked with mpmath against `e^ζ E₁(ζ)`.
- [2.5.E49](https://dlmf.nist.gov/2.5.E49): [`DLMF.AsymptoticApproximations.laplace_inv_one_add_eq`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L242) (proved); [`DLMF.AsymptoticApproximations.laplace_inv_one_add_eq_complex`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L266) (admitted). Proved for real `ζ > 0` from 6.2.2 (`DLMF.Confluent.expIntE1_stieltjes`) by `t ↦ ζt`; complex `ℜζ > 0` admitted.
- [2.5.T1](https://dlmf.nist.gov/2.5.T1): [`DLMF.AsymptoticApproximations.mellinConvergent_truncLow`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L151) (proved); [`DLMF.AsymptoticApproximations.mellinConvergent_truncHigh`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L171) (proved); [`DLMF.AsymptoticApproximations.mellinConvergent_trunc_h`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L194) (proved). Each row from O-bounds at `0⁺` and `∞` via Mathlib `mellinConvergent_of_isBigO_rpow` (implied by 2.5.17–2.5.20).
- [2.5.T2](https://dlmf.nist.gov/2.5.T2): [`DLMF.AsymptoticApproximations.mellinConvergent_pairs`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L206) (proved).

### Prose, informal and excluded items (part g2a)

Prose IDs carrying tags or pointers:

- [2.1.i](https://dlmf.nist.gov/2.1.i): [`DLMF.AsymptoticApproximations.cexp_neg_isLittleO_one_sector`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L56) (proved); [`DLMF.AsymptoticApproximations.not_cexp_neg_isLittleO_one_halfPlane`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L73) (proved); upstream [`Asymptotics.isBigO_top`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L42) (exact: f = O(g) in a region (the filter ⊤): |f| ≤ C|g| everywhere).
- [2.1.ii](https://dlmf.nist.gov/2.1.ii): [`DLMF.AsymptoticApproximations.ritt_isBigO`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L204) (admitted); [`DLMF.AsymptoticApproximations.ritt_isLittleO`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L216) (admitted).
- [2.1.iii](https://dlmf.nist.gov/2.1.iii): [`DLMF.AsymptoticApproximations.hasPoincareExpansion_of_hasSum`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L277) (proved); [`DLMF.AsymptoticApproximations.HasPoincareExpansion.add`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L314) (proved); [`DLMF.AsymptoticApproximations.HasPoincareExpansion.sub`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L321) (proved); [`DLMF.AsymptoticApproximations.HasPoincareExpansion.mul`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L328) (proved); [`DLMF.AsymptoticApproximations.HasPoincareExpansion.inv`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L338) (proved); [`DLMF.AsymptoticApproximations.HasPoincareExpansion.pow`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L348) (proved); [`DLMF.AsymptoticApproximations.HasPoincareExpansion.unique`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L357) (proved); [`DLMF.AsymptoticApproximations.HasPoincareExpansionAt.unique`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L370) (proved); [`DLMF.AsymptoticApproximations.hasPoincareExpansion_cexp_neg`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L399) (proved); [`DLMF.AsymptoticApproximations.hasPoincareExpansion_cexp_neg_sqrt`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L431) (admitted); [`DLMF.AsymptoticApproximations.exists_hasPoincareExpansion_sector`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L439) (admitted); upstream [`Asymptotics.HasAsymptoticExpansion.unique`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L54) (exact: uniqueness of the coefficients of an expansion on an asymptotic scale (DLMFMathlib)); upstream [`Asymptotics.HasAsymptoticExpansion.add`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L56) (exact: expansions can be added (DLMFMathlib)).
- [2.1.iv](https://dlmf.nist.gov/2.1.iv): [`DLMF.AsymptoticApproximations.hasUniformPoincareExpansion_iff`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L450) (admitted).
- [2.1.v](https://dlmf.nist.gov/2.1.v): [`DLMF.AsymptoticApproximations.hasGeneralizedAsymptoticExpansion_convergent_ne`](DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean#L463) (proved).
- [2.2](https://dlmf.nist.gov/2.2): [`DLMF.AsymptoticApproximations.existsUnique_root_of_isEquivalent`](DLMF/AsymptoticApproximations/Basics/Transcendental.lean#L30) (proved); [`DLMF.AsymptoticApproximations.root_isEquivalent`](DLMF/AsymptoticApproximations/Basics/Transcendental.lean#L46) (proved); upstream [`Asymptotics.HasAsymptoticPowerSeries.inversion`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L64) (stronger: reversion of an asymptotic power series w ∼ P(σ), P(0) = 0, P'(0) ≠ 0 (DLMFMathlib)).
- [2.3.i](https://dlmf.nist.gov/2.3.i): [`DLMF.AsymptoticApproximations.laplace_error_bound`](DLMF/AsymptoticApproximations/Integrals/Parts.lean#L79) (admitted); [`DLMF.AsymptoticApproximations.fourier_error_bound`](DLMF/AsymptoticApproximations/Integrals/Parts.lean#L107) (admitted); [`DLMF.AsymptoticApproximations.fourier_Ioi_hasGeneralizedAsymptoticExpansion`](DLMF/AsymptoticApproximations/Integrals/Parts.lean#L119) (admitted).
- [2.3.ii](https://dlmf.nist.gov/2.3.ii): [`DLMF.AsymptoticApproximations.watson_lemma`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L89) (proved).
- [2.3.iii](https://dlmf.nist.gov/2.3.iii): upstream [`Complex.isEquivalent_integral_laplace_Icc`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L78) (special case: leading term of Laplace's method at an interior quadratic minimum (lean-codes)); [`DLMF.AsymptoticApproximations.laplace_method`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L38) (admitted); [`DLMF.AsymptoticApproximations.laplace_method_Ioi`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L66) (admitted).
- [2.3.iv](https://dlmf.nist.gov/2.3.iv): [`DLMF.AsymptoticApproximations.stationaryPhase_watson`](DLMF/AsymptoticApproximations/Integrals/StationaryPhase.lean#L38) (admitted); [`DLMF.AsymptoticApproximations.stationaryPhase_endpoint`](DLMF/AsymptoticApproximations/Integrals/StationaryPhase.lean#L59) (admitted); [`DLMF.AsymptoticApproximations.stationaryPhase_endpoint_infinite`](DLMF/AsymptoticApproximations/Integrals/StationaryPhase.lean#L90) (admitted).
- [2.3.v](https://dlmf.nist.gov/2.3.v): [`DLMF.AsymptoticApproximations.bleisteinW_zero`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L54) (proved); [`DLMF.AsymptoticApproximations.bleisteinW_self`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L65) (proved); [`DLMF.AsymptoticApproximations.bleisteinW_hasDerivAt_self`](DLMF/AsymptoticApproximations/Integrals/Coalescing.lean#L99) (admitted).
- [2.4.i](https://dlmf.nist.gov/2.4.i): upstream [`hasAsymptoticExpansion_integral_cexp_smul_rotate`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L76) (exact: Watson's lemma after rotation of the path of integration (DLMFMathlib)); [`DLMF.AsymptoticApproximations.watson_lemma_sector`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L217) (proved); [`DLMF.AsymptoticApproximations.watson_lemma_rotate`](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L246) (admitted).
- [2.4.iii](https://dlmf.nist.gov/2.4.iii): [`DLMF.AsymptoticApproximations.laplace_method_contour`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L160) (admitted).
- [2.4.iv](https://dlmf.nist.gov/2.4.iv): [`DLMF.AsymptoticApproximations.saddle_point`](DLMF/AsymptoticApproximations/Integrals/Laplace.lean#L217) (admitted).
- [2.5.i](https://dlmf.nist.gov/2.5.i): upstream [`mellinConvergent_of_isBigO_rpow`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L86) (exact: the strip of convergence a < ℜz < b from O-bounds at 0 and ∞); upstream [`mellin_differentiableAt_of_isBigO_rpow`](DLMF/AsymptoticApproximations/Basics/MathlibCoverage.lean#L88) (exact: analyticity of 𝓜f in the strip of convergence); [`DLMF.AsymptoticApproximations.mellin_convolution_eq_mellinInv`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L53) (proved from admissions); [`DLMF.AsymptoticApproximations.besselSqMellinA_two_mul`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L109) (proved); [`DLMF.AsymptoticApproximations.besselSqMellinB_two_mul`](DLMF/AsymptoticApproximations/Mellin/BesselExample.lean#L125) (proved).
- [2.5.ii](https://dlmf.nist.gov/2.5.ii): [`DLMF.AsymptoticApproximations.mellinConvergent_truncLow`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L151) (proved); [`DLMF.AsymptoticApproximations.mellin_truncLow_continuation`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L233) (admitted); [`DLMF.AsymptoticApproximations.mellin_truncHigh_continuation`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L261) (admitted); [`DLMF.AsymptoticApproximations.mellin_truncHigh_continuation_osc`](DLMF/AsymptoticApproximations/Mellin/Transforms.lean#L276) (admitted).
- [2.5.iii](https://dlmf.nist.gov/2.5.iii): [`DLMF.AsymptoticApproximations.laplace_truncLow_shift`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L97) (admitted); [`DLMF.AsymptoticApproximations.laplace_truncHigh_shift`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L109) (admitted); [`DLMF.AsymptoticApproximations.laplace_remainder_isBigO`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L153) (proved); [`DLMF.AsymptoticApproximations.laplace_small_parameter`](DLMF/AsymptoticApproximations/Mellin/SmallParameter.lean#L198) (admitted).

Not formalized:

- §2.1(i), notation for `∼`, `o`, `O` "as `x → c` in `X`" and the remarks on uniformity: no
  statement (notation); covered by the filters in the statements and the pointers for 2.1.1–2.1.3.
- [2.1.iii](https://dlmf.nist.gov/2.1.iii) p5 (several Poincaré expansions interpreted
  separately; example 2.8.15): excluded: informal; the convention is used in 2.3.23 and 2.5.44.
- [2.1.v](https://dlmf.nist.gov/2.1.v) p2 (multiplication of generalized expansions may fail;
  §18.15(iii) example): excluded: informal. The convergent-but-wrong-sum phenomenon is
  `hasGeneralizedAsymptoticExpansion_convergent_ne` (proved).
- [2.3.ii](https://dlmf.nist.gov/2.3.ii) p2 (Watson's lemma is the most used method; finite
  ranges included; references): excluded: informal. Finite ranges are covered since `q` need
  only satisfy the integrability hypothesis.
- [2.3.iii](https://dlmf.nist.gov/2.3.iii) p3 (Watson's lemma as a special case of Laplace's
  method): excluded: informal.
- [2.3.vi](https://dlmf.nist.gov/2.3.vi) (asymptotics of Mellin transforms): no statement
  (references only).
- [2.4.i](https://dlmf.nist.gov/2.4.i) p3, [2.4.iii](https://dlmf.nist.gov/2.4.iii) p4,
  [2.4.v](https://dlmf.nist.gov/2.4.v) p3–p4, [2.4.vi](https://dlmf.nist.gov/2.4.vi): no
  statement (references only).
- [2.4.iv](https://dlmf.nist.gov/2.4.iv) p1–p2 (reduction to a saddle point by subdividing and
  deforming the path; terminology): excluded: informal; the resulting statement is
  `saddle_point` (2.4.15).
- [2.4.v](https://dlmf.nist.gov/2.4.v) p1–p2 (uniform approximation for two coalescing saddle
  points in terms of Airy functions, "similar to §2.3(v)"): excluded: informal beyond the change
  of variables 2.4.18–2.4.21 (`cfu_deriv`, `cfu_airy_form`, proved).
- [2.5.ii](https://dlmf.nist.gov/2.5.ii) p9–p10, §2.5(iii) Example p2: no statement (references
  only).

### Validation (part g2a)

- sympy: Lagrange reversion 2.2.8 (`F₁ = f₁`, `F₂ = f₀f₁ + f₂`, `F₃`); `b₀, b₁, b₂` of 2.3.17
  against 2.3.18; `b₀, b₂` of 2.4.16.
- mpmath: 2.3.15 (`p = t² + t³`, `q = 1 + 2t`, error `O(x⁻²)`); signs in 2.3.4 and 2.3.23;
  2.5.10 (three `(ν, z)` pairs, agreement to `10⁻⁷` with a truncated integral); 2.5.11/2.5.15
  sign (erratum above); 2.5.46 (`ζ = 0.3`, `k = 1, 2, 3`) and 2.5.47 by circle integrals;
  2.5.48 against `e^ζ E₁(ζ)`.
- Lean: every module checked with `lake env lean -DautoImplicit=false
  -DrelaxedAutoImplicit=false` and built with `lake build`; no warnings other than
  `declaration uses 'sorry'`; `#print axioms` run on all 71 public proved theorems (see Counts).

## Part g2b: §§2.6–2.11

This part of the Chapter 2 acquisition covers the definitions, numbered formulas and analytical
assertions in prose of [DLMF §§2.6–2.11](https://dlmf.nist.gov/2.6), version 1.2.8, checked on
2026-10-27, by agent g2b (helper prefix `g2b_`). Part g2a covers §§2.1–2.5. The Lean code is in
`DLMF/AsymptoticApproximations/{Distributional,ODE,Sums,Remainders}/` (namespace
`DLMF.AsymptoticApproximations`). Expansions use DLMFMathlib's
`Asymptotics.HasAsymptoticExpansion`; nothing depends on part g2a's files.

Modules, in import order:

- §2.6: [Distributional/Defs](DLMF/AsymptoticApproximations/Distributional/Defs.lean) (Mathlib
  only) → [Distributional/Stieltjes](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean)
  (also `DLMF.Gamma.BetaFunction`) →
  [Distributional/FractionalIntegrals](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean);
  [Distributional/MathlibCoverage](DLMF/AsymptoticApproximations/Distributional/MathlibCoverage.lean)
  (`DLMF.Core.Upstream` and Mathlib only).
- §§2.7–2.9: [ODE/Defs](DLMF/AsymptoticApproximations/ODE/Defs.lean) (definitions files
  `DLMF.Painleve.Defs`, `DLMF.Airy.Basic`, `DLMF.Bessel.Basic`, and
  `DLMFMathlib.Analysis.ODE.Singularities`) →
  [ODE/Singularities](DLMF/AsymptoticApproximations/ODE/Singularities.lean) (§2.7(i)–(ii), (iv)),
  [ODE/LiouvilleGreen](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean) (§2.7(iii)),
  [ODE/Parameter](DLMF/AsymptoticApproximations/ODE/Parameter.lean) (§2.8; also
  `DLMF.Bessel.Modified`), [ODE/Difference](DLMF/AsymptoticApproximations/ODE/Difference.lean)
  (§2.9).
- §2.10: [Sums/Defs](DLMF/AsymptoticApproximations/Sums/Defs.lean) (Mathlib and
  `DLMFMathlib.Analysis.EulerMaclaurin`) →
  [Sums/EulerMaclaurin](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean) (§2.10(i)–(ii);
  also `DLMF.Gamma.BarnesG`), [Sums/Darboux](DLMF/AsymptoticApproximations/Sums/Darboux.lean)
  (§2.10(iii)–(iv); also `DLMF.GeneralizedHypergeometric.Basic`,
  `DLMF.OrthogonalPolynomials.Series`);
  [Sums/MathlibCoverage](DLMF/AsymptoticApproximations/Sums/MathlibCoverage.lean).
- §2.11: [Remainders/Defs](DLMF/AsymptoticApproximations/Remainders/Defs.lean) (Mathlib only) →
  [Remainders/Stokes](DLMF/AsymptoticApproximations/Remainders/Stokes.lean) (also `ODE/Defs`,
  `DLMF.IncompleteGamma.ExpIntegralAsymptotics`, `DLMF.ExpIntegrals.Asymptotics`,
  `DLMF.Confluent.Asymptotics`, `DLMF.Confluent.Basic`).

**Counts.** §§2.6–2.11 have 217 numbered equations (2.6: 62, 2.7: 37, 2.8: 36, 2.9: 14,
2.10: 36, 2.11: 32). Excluded: 8 (6 excluded: numerical, 2.11.4, 2.11.25–2.11.28, 2.11.31, and
Table 2.11.1; 1 excluded: informal, 2.6.31; 1 no statement (references only), 2.9.14). In
scope: 209, all covered: 207 by local declarations and 2 (2.6.58, 2.6.61) by Mathlib pointers.
Of the 209, 47 carry a proved theorem, 32 are covered by definitions only, 2 by upstream
pointers only and 128 by admitted theorems (11 of these also by definitions). In addition 16
prose IDs carry tags (2.6.iii, 2.7.i–iv, 2.8.i–iv, 2.9.i–ii, 2.10.i, 2.10.iv, 2.11.iii–v).
225 DLMF IDs are tagged or pointed to, on 179 tagged declarations and 4 `dlmf_upstream`
pointers (2.6.E58, 2.6.E61, 2.10.E8, 2.10.E9). The 221 declarations are 89 definitions
(all in the `Defs` files), 49 proved theorems (of which 4 untagged helpers) and 83 direct
admissions. Exactly one proved theorem depends on an admission
(`kPlusPairing_powKernel_conv_log`, 2.6.40, from the admitted function identity
`halfLineConvolution_powKernel_log`).

Module admissions (`grep -cE 'by sorry|:= sorry|^\s*(·\s*)?sorry\s*$|exact sorry'`):

- Distributional/Defs 0 (32 definitions); Distributional/Stieltjes 11 (3 proved);
  Distributional/FractionalIntegrals 14 (4 proved); Distributional/MathlibCoverage 0
  (2 pointers).
- ODE/Defs 0 (31 definitions); ODE/Singularities 8 (6 proved); ODE/LiouvilleGreen 5 (2 proved);
  ODE/Parameter 7 (7 proved); ODE/Difference 7 (2 proved).
- Sums/Defs 0 (19 definitions); Sums/EulerMaclaurin 12 (8 proved); Sums/Darboux 12
  (6 proved); Sums/MathlibCoverage 0 (2 pointers).
- Remainders/Defs 0 (7 definitions); Remainders/Stokes 7 (11 proved).

### Domains, conventions and source corrections (part g2b)

- **Erratum, §2.10(iv) (2.10.34–2.10.36).** DLMF takes `α ∈ (0, 2π)` in the Legendre example;
  the formulas need `α ∈ (0, π)`. For `π < α < 2π`, `sin α < 0`, so `(2 sin α)^{-1/2}` in
  2.10.34–2.10.35 and the right side of 2.10.36 are not real, while `P_n(cos α)` is real; with
  `α' = 2π - α ∈ (0, π)` one has `P_n(cos α) = P_n(cos α')` and the correct phase is
  `nα' + α'/2 - π/4`, which is not `nα + α/2 - π/4`. Numerically 2.10.35–2.10.36 hold for
  `α = 0.9, 2.5`. Tagged `@[dlmf 2.10.E35 "corrected: …"]`, `@[dlmf 2.10.E36 "corrected: …"]`.
- **Expansions.** `f ∼ ∑ a_s φ_s` is `HasAsymptoticExpansion l φ a f` (for every `N`,
  `f - ∑_{s<N} φ_s a_s = O(φ_N)`). Uniform statements ("as `u → ∞` uniformly in `ξ`") are
  written with explicit constants `∃ C U₀, ∀ u ≥ U₀, ∀ ξ, …`.
- **Sectors beyond `2π`.** Solutions at a rank-one irregular singularity (2.7.14–2.7.17,
  2.11.19–2.11.23) and `E_p(z)` in `|ph z| ≤ 3π/2 - δ`, `π/2 + δ ≤ ph z ≤ 7π/2 - δ`,
  `-π + δ ≤ ph z ≤ 3π - δ` (2.11.6, 2.11.7, 2.11.15) live on the logarithmic plane `z = e^ζ`
  (the project's `genExpIntEOnLog`, `logSector`, and the local `logSectorFilter`).
- **§2.6.** Distributions are represented by their pairings with test functions; the Stieltjes
  transform results use `IsStieltjesExpansion` and the analytic continuation hypothesis
  `IsMellinContinuation` (holomorphy off `k + α`, agreement with `mellin` on the strip). The
  test variable is `u` (the letter `φ` is Mathlib's totient notation under `open scoped Nat`).
- **§2.7(i).** Ordinary and regular singular points use DLMFMathlib's
  `Complex.linearODEOrdinaryAt`/`linearODERegularSingularAt` with coefficients `![g, f]`;
  `linearODERegularSingularAt_iff` (proved) gives DLMF's description.
- **§2.8.** Case I (2.8.10–2.8.13) is proved for real `ξ` from DLMFMathlib's Liouville–Green
  expansions with error bounds (Olver Ch. 10, Thm 3.1) with amplitude 1: stronger than DLMF,
  explicit bounds `u^{-n} 𝒱(A_n) exp(𝒱(ψ)/(2u))`. Cases II and III (Airy and Bessel
  approximants, envelope functions 2.8.19–2.8.21, 2.8.32–2.8.34) are admitted.
- **§2.10(i).** `euler_maclaurin` (2.10.1) is proved from DLMFMathlib's
  `sum_range_succ_eq_integral_add` for `f ∈ C^{2m}(ℝ)` (DLMF assumes only absolute integrability
  of `f^{(2m)}` on `[a, n]`; the formal hypothesis is stronger). Bernoulli numbers are Mathlib's
  `bernoulli` (`B₁ = -1/2`, as in DLMF §24.2), `B̃_n` is DLMFMathlib's `periodicBernoulli`. The
  constant `C` of 2.10.4 is `ln A` with the project's Glaisher–Kinkelin constant
  (5.17.6–5.17.7); 2.10.6 and the leading-order form of 2.10.4 are proved from it. The
  remainder bounds of §2.10(i) for 2.10.7 and 2.10.8 were checked numerically for
  `n = 1, 2, 3, 5, 10` and several `α`, `m` and are admitted for all `n ≥ 1`.
- **§2.10(iii).** The contour `𝒞` of Figure 2.10.1 is the right semicircle `|t| = n - ½`, the
  imaginary axis down to `i/2`, the left semicircle `|t| = ½` and the imaginary axis down to
  `-i(n-½)` (`contourIntegralC`, with halves `contourIntegralC₁`, `contourIntegralC₂`);
  `₀F₂(-; 1, 1; x)` is matched with the project's `genCoeff` (16.2.1) and
  `genSeriesConvergesTo`.
- **§2.10(iv).** Laurent coefficients are circle integrals (`laurentCoeff`); `n → ±∞` is the
  cofinite filter on `ℤ`; the branches of `(e^{∓iα} - z)^{-1/2}` in 2.10.34 are
  `e^{±iα/2}(1 - z e^{±iα})^{-1/2}` with the principal power.
- **§2.11.** `c(θ)` (2.11.16) is `(π-θ) (2(1+e^{iθ}+i(θ-π))/(π-θ)²)^{1/2}` with the principal
  root (continuous on `(-π, 3π)`, `c(θ) ∼ π - θ`); `c(θ)² = 2(1+e^{iθ}+i(θ-π))` is proved. The
  coefficients `a_{2s}(θ, α)` of 2.11.13 are only specified for `s = 0, 1` and are existentially
  quantified. The terminant `F_{n+p}(z) = Γ(n+p)/(2π) E_{n+p}(z)/z^{n+p-1}` is written out in
  the statements (`E_p` is defined in a theorem file of the confluent area). 2.11.29–2.11.30
  are proved for real `x → +∞` from the project's 13.19.3 (DLMF: `|ph z| ≤ 3π/2 - δ`).
- **Upstream pointers.** 2.6.58 (`not_integrableOn_Ioi_rpow`, exact), 2.6.61
  (`mellin_comp_mul_left`, stronger), 2.10.8 (`Real.tendsto_harmonic_sub_log`, partial),
  2.10.9 (`Finset.sum_range_by_parts`, different convention).

### Numbered formulas and prose items (part g2b)

## [§2.6 Distributional Methods](https://dlmf.nist.gov/2.6)

- [2.6.E1](https://dlmf.nist.gov/2.6.E1): [`DLMF.AsymptoticApproximations.stieltjesCubeRootExample`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L174) (definition); [`DLMF.AsymptoticApproximations.stieltjesCubeRootExample_expansion`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L129) (admitted)
- [2.6.E2](https://dlmf.nist.gov/2.6.E2): [`DLMF.AsymptoticApproximations.one_add_rpow_neg_third_hasSum`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L38) (proved)
- [2.6.E3](https://dlmf.nist.gov/2.6.E3): [`DLMF.AsymptoticApproximations.not_integrableOn_rpow_div_add`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L65) (admitted)
- [2.6.E4](https://dlmf.nist.gov/2.6.E4): [`DLMF.AsymptoticApproximations.integral_rpow_div_add_cpow`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L72) (proved)
- [2.6.E5](https://dlmf.nist.gov/2.6.E5): [`DLMF.AsymptoticApproximations.gamma_two_thirds_sub_mul_gamma`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L112) (proved)
- [2.6.E6](https://dlmf.nist.gov/2.6.E6): [`DLMF.AsymptoticApproximations.not_stieltjesCubeRootExample_naive`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L140) (admitted)
- [2.6.E7](https://dlmf.nist.gov/2.6.E7): [`DLMF.AsymptoticApproximations.stieltjesCubeRootExample_expansion`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L129) (admitted)
- [2.6.E8](https://dlmf.nist.gov/2.6.E8): [`DLMF.AsymptoticApproximations.stieltjesTransform`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L44) (definition)
- [2.6.E9](https://dlmf.nist.gov/2.6.E9): [`DLMF.AsymptoticApproximations.IsStieltjesExpansion`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L132) (definition)
- [2.6.E10](https://dlmf.nist.gov/2.6.E10): [`DLMF.AsymptoticApproximations.IsStieltjesExpansion`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L132) (definition); [`DLMF.AsymptoticApproximations.stieltjesRemainder`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L144) (definition)
- [2.6.E11](https://dlmf.nist.gov/2.6.E11): [`DLMF.AsymptoticApproximations.functionPairing`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L57) (definition)
- [2.6.E12](https://dlmf.nist.gov/2.6.E12): [`DLMF.AsymptoticApproximations.functionPairing`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L57) (definition); [`DLMF.AsymptoticApproximations.tPowPairing`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L77) (definition)
- [2.6.E13](https://dlmf.nist.gov/2.6.E13): [`DLMF.AsymptoticApproximations.powPairing`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L63) (definition); [`DLMF.AsymptoticApproximations.tPowPairing`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L77) (definition)
- [2.6.E14](https://dlmf.nist.gov/2.6.E14): [`DLMF.AsymptoticApproximations.logPowPairing`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L71) (definition); [`DLMF.AsymptoticApproximations.tPowPairing`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L77) (definition)
- [2.6.E15](https://dlmf.nist.gov/2.6.E15): [`DLMF.AsymptoticApproximations.repeatedTailIntegral`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L92) (definition)
- [2.6.E16](https://dlmf.nist.gov/2.6.E16): [`DLMF.AsymptoticApproximations.remainderPairing`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L99) (definition)
- [2.6.E17](https://dlmf.nist.gov/2.6.E17): [`DLMF.AsymptoticApproximations.functionPairing_eq_of_lt_one`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L151) (admitted)
- [2.6.E18](https://dlmf.nist.gov/2.6.E18): [`DLMF.AsymptoticApproximations.stieltjesDeltaCoeff`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L187) (definition)
- [2.6.E19](https://dlmf.nist.gov/2.6.E19): [`DLMF.AsymptoticApproximations.diracDerivPairing`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L87) (definition)
- [2.6.E20](https://dlmf.nist.gov/2.6.E20): [`DLMF.AsymptoticApproximations.functionPairing_eq_of_eq_one`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L166) (admitted)
- [2.6.E21](https://dlmf.nist.gov/2.6.E21): [`DLMF.AsymptoticApproximations.stieltjesLogDeltaCoeff`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L198) (definition)
- [2.6.E22](https://dlmf.nist.gov/2.6.E22): [`DLMF.AsymptoticApproximations.stieltjesTestFunction`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L106) (definition)
- [2.6.E23](https://dlmf.nist.gov/2.6.E23): [`DLMF.AsymptoticApproximations.tendsto_powPairing_stieltjesTestFunction`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L180) (admitted)
- [2.6.E24](https://dlmf.nist.gov/2.6.E24): [`DLMF.AsymptoticApproximations.tendsto_logPowPairing_stieltjesTestFunction`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L189) (admitted)
- [2.6.E25](https://dlmf.nist.gov/2.6.E25): [`DLMF.AsymptoticApproximations.tendsto_functionPairing_stieltjesTestFunction`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L199) (admitted)
- [2.6.E26](https://dlmf.nist.gov/2.6.E26): [`DLMF.AsymptoticApproximations.tendsto_remainderPairing_stieltjesTestFunction`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L209) (admitted)
- [2.6.E27](https://dlmf.nist.gov/2.6.E27): [`DLMF.AsymptoticApproximations.stieltjesTransform_eq_of_lt_one`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L225) (admitted)
- [2.6.E28](https://dlmf.nist.gov/2.6.E28): [`DLMF.AsymptoticApproximations.stieltjesTransform_eq_of_eq_one`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L238) (admitted)
- [2.6.E29](https://dlmf.nist.gov/2.6.E29): [`DLMF.AsymptoticApproximations.stieltjesLogCoeff`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L193) (definition); [`DLMF.AsymptoticApproximations.stieltjesTransform_eq_of_eq_one`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L238) (admitted)
- [2.6.E30](https://dlmf.nist.gov/2.6.E30): [`DLMF.AsymptoticApproximations.stieltjesRemainderTerm`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L149) (definition); [`DLMF.AsymptoticApproximations.stieltjesTransform_eq_of_lt_one`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L225) (admitted)
- [2.6.E31](https://dlmf.nist.gov/2.6.E31): excluded: informal (the hypothesis class `f(t) ∼ e^{ict} ∑ a_s t^{-s-α}` for which "similar results hold"; references only)
- [2.6.E32](https://dlmf.nist.gov/2.6.E32): [`DLMF.AsymptoticApproximations.generalizedStieltjesTransform`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L51) (definition)
- [2.6.E33](https://dlmf.nist.gov/2.6.E33): [`DLMF.AsymptoticApproximations.riemannLiouvilleIntegral`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L112) (definition)
- [2.6.E34](https://dlmf.nist.gov/2.6.E34): [`DLMF.AsymptoticApproximations.halfLineConvolution`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L118) (definition)
- [2.6.E35](https://dlmf.nist.gov/2.6.E35): [`DLMF.AsymptoticApproximations.riemannLiouvilleIntegral_eq_convolution`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L32) (proved)
- [2.6.E36](https://dlmf.nist.gov/2.6.E36): [`DLMF.AsymptoticApproximations.integrableOn_powKernel_mul_rpow_iff`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L38) (admitted)
- [2.6.E37](https://dlmf.nist.gov/2.6.E37): [`DLMF.AsymptoticApproximations.kPlusPairing_convolution_congr`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L62) (admitted)
- [2.6.E38](https://dlmf.nist.gov/2.6.E38): [`DLMF.AsymptoticApproximations.kPlusPairing_powKernel_conv_delta`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L77) (admitted)
- [2.6.E39](https://dlmf.nist.gov/2.6.E39): [`DLMF.AsymptoticApproximations.kPlusPairing_powKernel_conv_rpow`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L87) (admitted)
- [2.6.E40](https://dlmf.nist.gov/2.6.E40): [`DLMF.AsymptoticApproximations.halfLineConvolution_powKernel_log`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L101) (admitted); [`DLMF.AsymptoticApproximations.kPlusPairing_powKernel_conv_log`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L109) (proved from admissions)
- [2.6.E41](https://dlmf.nist.gov/2.6.E41): [`DLMF.AsymptoticApproximations.functionPairing_eq_of_lt_one`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L151) (admitted)
- [2.6.E42](https://dlmf.nist.gov/2.6.E42): [`DLMF.AsymptoticApproximations.functionPairing_eq_of_eq_one`](DLMF/AsymptoticApproximations/Distributional/Stieltjes.lean#L166) (admitted)
- [2.6.E43](https://dlmf.nist.gov/2.6.E43): [`DLMF.AsymptoticApproximations.riemannLiouvilleIntegral_eq_of_lt_one`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L128) (admitted)
- [2.6.E44](https://dlmf.nist.gov/2.6.E44): [`DLMF.AsymptoticApproximations.riemannLiouvilleIntegral_eq_of_eq_one`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L144) (admitted)
- [2.6.E45](https://dlmf.nist.gov/2.6.E45): [`DLMF.AsymptoticApproximations.riemannLiouvilleIntegral_eq_of_lt_one`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L128) (admitted)
- [2.6.E46](https://dlmf.nist.gov/2.6.E46): [`DLMF.AsymptoticApproximations.riemannLiouvilleIntegral_eq_of_eq_one`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L144) (admitted)
- [2.6.E47](https://dlmf.nist.gov/2.6.E47): [`DLMF.AsymptoticApproximations.fractionalRemainder`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L232) (definition)
- [2.6.E48](https://dlmf.nist.gov/2.6.E48): [`DLMF.AsymptoticApproximations.riemannLiouvilleIntegral_exampleF`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L180) (admitted)
- [2.6.E49](https://dlmf.nist.gov/2.6.E49): [`DLMF.AsymptoticApproximations.g2b_exampleF_eq`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L162) (admitted)
- [2.6.E50](https://dlmf.nist.gov/2.6.E50): [`DLMF.AsymptoticApproximations.g2b_exampleF_eq`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L162) (admitted)
- [2.6.E51](https://dlmf.nist.gov/2.6.E51): [`DLMF.AsymptoticApproximations.g2b_exampleF_mellin`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L171) (admitted)
- [2.6.E52](https://dlmf.nist.gov/2.6.E52): [`DLMF.AsymptoticApproximations.riemannLiouvilleIntegral_exampleF`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L180) (admitted)
- [2.6.E53](https://dlmf.nist.gov/2.6.E53): [`DLMF.AsymptoticApproximations.norm_fractionalRemainder_exampleF_le`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L198) (admitted)
- [2.6.E54](https://dlmf.nist.gov/2.6.E54): [`DLMF.AsymptoticApproximations.mellinConvolutionIntegral`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L161) (definition)
- [2.6.E55](https://dlmf.nist.gov/2.6.E55): [`DLMF.AsymptoticApproximations.mul_comp_mul_eq_expansion`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L212) (admitted); [`DLMF.AsymptoticApproximations.mellin_continuation_eq_mellin_remainder`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L247) (admitted)
- [2.6.E56](https://dlmf.nist.gov/2.6.E56): [`DLMF.AsymptoticApproximations.mul_comp_mul_eq_expansion`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L212) (admitted)
- [2.6.E57](https://dlmf.nist.gov/2.6.E57): [`DLMF.AsymptoticApproximations.mul_comp_mul_eq_expansion`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L212) (admitted)
- [2.6.E58](https://dlmf.nist.gov/2.6.E58): Mathlib [`not_integrableOn_Ioi_rpow`](DLMF/AsymptoticApproximations/Distributional/MathlibCoverage.lean#L18) (upstream pointer)
- [2.6.E59](https://dlmf.nist.gov/2.6.E59): [`DLMF.AsymptoticApproximations.regularized_integral_rpow_eq_zero`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L229) (proved)
- [2.6.E60](https://dlmf.nist.gov/2.6.E60): [`DLMF.AsymptoticApproximations.mellin_continuation_eq_mellin_remainder`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L247) (admitted)
- [2.6.E61](https://dlmf.nist.gov/2.6.E61): Mathlib [`mellin_comp_mul_left`](DLMF/AsymptoticApproximations/Distributional/MathlibCoverage.lean#L21) (upstream pointer)
- [2.6.E62](https://dlmf.nist.gov/2.6.E62): [`DLMF.AsymptoticApproximations.mellinConvolutionIntegral_eq`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L263) (admitted)
- [2.6.iii](https://dlmf.nist.gov/2.6.iii) (prose): [`DLMF.AsymptoticApproximations.kPlusPairing`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L124) (definition); [`DLMF.AsymptoticApproximations.halfLineConvolution_comm`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L48) (proved)
- [2.6.iii](https://dlmf.nist.gov/2.6.iii): [`DLMF.AsymptoticApproximations.halfLineConvolution_comm`](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L48) (proved); [`DLMF.AsymptoticApproximations.kPlusPairing`](DLMF/AsymptoticApproximations/Distributional/Defs.lean#L124) (definition).

## [§2.7 Differential Equations](https://dlmf.nist.gov/2.7)

- [2.7.E1](https://dlmf.nist.gov/2.7.E1): [`DLMF.AsymptoticApproximations.IsLinearODE2SolOn`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L44) (definition); [`DLMF.AsymptoticApproximations.IsLogPlaneSolOn`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L50) (definition)
- [2.7.E2](https://dlmf.nist.gov/2.7.E2): [`DLMF.AsymptoticApproximations.frobenius_solutions`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L69) (admitted)
- [2.7.E3](https://dlmf.nist.gov/2.7.E3): [`DLMF.AsymptoticApproximations.indicialPoly`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L58) (definition); [`DLMF.AsymptoticApproximations.frobenius_solutions`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L69) (admitted)
- [2.7.E4](https://dlmf.nist.gov/2.7.E4): [`DLMF.AsymptoticApproximations.frobenius_solutions`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L69) (admitted)
- [2.7.E5](https://dlmf.nist.gov/2.7.E5): [`DLMF.AsymptoticApproximations.frobeniusCoeff`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L62) (definition); [`DLMF.AsymptoticApproximations.frobenius_solutions`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L69) (admitted)
- [2.7.E6](https://dlmf.nist.gov/2.7.E6): [`DLMF.AsymptoticApproximations.frobenius_log_solution`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L93) (admitted)
- [2.7.E7](https://dlmf.nist.gov/2.7.E7): [`DLMF.AsymptoticApproximations.rankOne_exists_unique_solutions`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L140) (admitted)
- [2.7.E8](https://dlmf.nist.gov/2.7.E8): [`DLMF.AsymptoticApproximations.rankOneCoeff`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L89) (definition); [`DLMF.AsymptoticApproximations.rankOne_exists_unique_solutions`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L140) (admitted)
- [2.7.E9](https://dlmf.nist.gov/2.7.E9): [`DLMF.AsymptoticApproximations.characteristic_roots_eq_iff`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L127) (proved)
- [2.7.E10](https://dlmf.nist.gov/2.7.E10): [`DLMF.AsymptoticApproximations.rankOneExponent`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L83) (definition)
- [2.7.E11](https://dlmf.nist.gov/2.7.E11): [`DLMF.AsymptoticApproximations.rankOneCoeff`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L89) (definition)
- [2.7.E12](https://dlmf.nist.gov/2.7.E12): [`DLMF.AsymptoticApproximations.rankOne_late_coefficients`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L188) (admitted)
- [2.7.E13](https://dlmf.nist.gov/2.7.E13): [`DLMF.AsymptoticApproximations.rankOne_late_coefficients`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L188) (admitted)
- [2.7.E14](https://dlmf.nist.gov/2.7.E14): [`DLMF.AsymptoticApproximations.rankOne_exists_unique_solutions`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L140) (admitted)
- [2.7.E15](https://dlmf.nist.gov/2.7.E15): [`DLMF.AsymptoticApproximations.rankOne_exists_unique_solutions`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L140) (admitted)
- [2.7.E16](https://dlmf.nist.gov/2.7.E16): [`DLMF.AsymptoticApproximations.rankOne_exists_unique_solutions`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L140) (admitted)
- [2.7.E17](https://dlmf.nist.gov/2.7.E17): [`DLMF.AsymptoticApproximations.rankOne_stokes_multipliers`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L168) (admitted)
- [2.7.E18](https://dlmf.nist.gov/2.7.E18): [`DLMF.AsymptoticApproximations.rankOne_late_coefficients`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L188) (admitted)
- [2.7.E19](https://dlmf.nist.gov/2.7.E19): [`DLMF.AsymptoticApproximations.fabry_transformation`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L221) (admitted)
- [2.7.E20](https://dlmf.nist.gov/2.7.E20): [`DLMF.AsymptoticApproximations.liouvilleGreen_interval`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L36) (admitted); [`DLMF.AsymptoticApproximations.liouvilleGreen_recessive_atTop`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L58) (proved)
- [2.7.E21](https://dlmf.nist.gov/2.7.E21): [`DLMF.AsymptoticApproximations.liouvilleGreen_interval`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L36) (admitted)
- [2.7.E22](https://dlmf.nist.gov/2.7.E22): [`DLMF.AsymptoticApproximations.liouvilleGreen_interval`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L36) (admitted); [`DLMF.AsymptoticApproximations.liouvilleGreen_recessive_atTop`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L58) (proved)
- [2.7.E23](https://dlmf.nist.gov/2.7.E23): [`DLMF.AsymptoticApproximations.liouvilleGreen_interval`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L36) (admitted); [`DLMF.AsymptoticApproximations.liouvilleGreen_recessive_atTop`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L58) (proved)
- [2.7.E24](https://dlmf.nist.gov/2.7.E24): [`DLMF.AsymptoticApproximations.liouvilleGreen_interval`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L36) (admitted)
- [2.7.E25](https://dlmf.nist.gov/2.7.E25): [`DLMF.AsymptoticApproximations.liouvilleGreen_interval`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L36) (admitted)
- [2.7.E26](https://dlmf.nist.gov/2.7.E26): [`DLMF.AsymptoticApproximations.liouvilleGreen_interval_isEquivalent`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L117) (admitted)
- [2.7.E27](https://dlmf.nist.gov/2.7.E27): [`DLMF.AsymptoticApproximations.liouvilleGreen_recessive_isEquivalent`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L90) (proved); [`DLMF.AsymptoticApproximations.liouvilleGreen_interval_isEquivalent`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L117) (admitted)
- [2.7.E28](https://dlmf.nist.gov/2.7.E28): [`DLMF.AsymptoticApproximations.liouvilleGreen_dominant`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L132) (admitted)
- [2.7.E29](https://dlmf.nist.gov/2.7.E29): [`DLMF.AsymptoticApproximations.liouvilleGreen_dominant`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L132) (admitted)
- [2.7.E30](https://dlmf.nist.gov/2.7.E30): [`DLMF.AsymptoticApproximations.liouvilleGreen_dominant`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L132) (admitted)
- [2.7.E31](https://dlmf.nist.gov/2.7.E31): [`DLMF.AsymptoticApproximations.liouvilleGreen_example`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L157) (admitted)
- [2.7.E32](https://dlmf.nist.gov/2.7.E32): [`DLMF.AsymptoticApproximations.sqrt_add_log_expansion`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L149) (admitted)
- [2.7.E33](https://dlmf.nist.gov/2.7.E33): [`DLMF.AsymptoticApproximations.liouvilleGreen_example`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L157) (admitted)
- [2.7.E34](https://dlmf.nist.gov/2.7.E34): [`DLMF.AsymptoticApproximations.liouvilleGreen_example`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L157) (admitted)
- [2.7.E35](https://dlmf.nist.gov/2.7.E35): [`DLMF.AsymptoticApproximations.eq_exp_combination`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L252) (proved)
- [2.7.E36](https://dlmf.nist.gov/2.7.E36): [`DLMF.AsymptoticApproximations.eq_exp_combination`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L252) (proved)
- [2.7.E37](https://dlmf.nist.gov/2.7.E37): [`DLMF.AsymptoticApproximations.eq_cosh_sinh_combination`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L284) (proved)
- [2.7.i](https://dlmf.nist.gov/2.7.i) (prose): [`DLMF.AsymptoticApproximations.exists_unique_solution_of_ordinary`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L37) (admitted); [`DLMF.AsymptoticApproximations.linearODERegularSingularAt_iff`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L51) (proved)
- [2.7.ii](https://dlmf.nist.gov/2.7.ii) (prose): [`DLMF.AsymptoticApproximations.HasSingularityRank`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L73) (definition); [`DLMF.AsymptoticApproximations.hasSingularityRank_zero_of_regularSingular`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L118) (proved); [`DLMF.AsymptoticApproximations.fabry_coefficients`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L233) (admitted)
- [2.7.iii](https://dlmf.nist.gov/2.7.iii) (prose): [`DLMF.AsymptoticApproximations.liouvilleGreen_dominant`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L132) (admitted)
- [2.7.iv](https://dlmf.nist.gov/2.7.iv) (prose): [`DLMF.AsymptoticApproximations.exp_div_exp_neg_tendsto`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L295) (proved)
- [2.7.i](https://dlmf.nist.gov/2.7.i): [`DLMF.AsymptoticApproximations.exists_unique_solution_of_ordinary`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L37) (admitted); [`DLMF.AsymptoticApproximations.linearODERegularSingularAt_iff`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L51) (proved).
- [2.7.ii](https://dlmf.nist.gov/2.7.ii): [`DLMF.AsymptoticApproximations.HasSingularityRank`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L73) (definition); [`DLMF.AsymptoticApproximations.fabry_coefficients`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L233) (admitted); [`DLMF.AsymptoticApproximations.hasSingularityRank_zero_of_regularSingular`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L118) (proved).
- [2.7.iii](https://dlmf.nist.gov/2.7.iii): [`DLMF.AsymptoticApproximations.liouvilleGreen_dominant`](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L132) (admitted).
- [2.7.iv](https://dlmf.nist.gov/2.7.iv): [`DLMF.AsymptoticApproximations.exp_div_exp_neg_tendsto`](DLMF/AsymptoticApproximations/ODE/Singularities.lean#L295) (proved).

## [§2.8 Differential Equations with a Parameter](https://dlmf.nist.gov/2.8)

- [2.8.E1](https://dlmf.nist.gov/2.8.E1): [`DLMF.AsymptoticApproximations.liouville_transformation`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L45) (admitted)
- [2.8.E2](https://dlmf.nist.gov/2.8.E2): [`DLMF.AsymptoticApproximations.liouville_transformation`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L45) (admitted)
- [2.8.E3](https://dlmf.nist.gov/2.8.E3): [`DLMF.AsymptoticApproximations.liouville_transformation`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L45) (admitted)
- [2.8.E4](https://dlmf.nist.gov/2.8.E4): [`DLMF.AsymptoticApproximations.liouville_transformation`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L45) (admitted)
- [2.8.E5](https://dlmf.nist.gov/2.8.E5): [`DLMF.AsymptoticApproximations.liouville_caseI`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L65) (proved)
- [2.8.E6](https://dlmf.nist.gov/2.8.E6): [`DLMF.AsymptoticApproximations.liouville_caseII`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L73) (proved)
- [2.8.E7](https://dlmf.nist.gov/2.8.E7): [`DLMF.AsymptoticApproximations.liouville_caseIII`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L94) (proved)
- [2.8.E8](https://dlmf.nist.gov/2.8.E8): [`DLMF.AsymptoticApproximations.liouville_caseI`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L65) (proved); [`DLMF.AsymptoticApproximations.liouville_caseII`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L73) (proved); [`DLMF.AsymptoticApproximations.liouville_caseIII`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L94) (proved)
- [2.8.E9](https://dlmf.nist.gov/2.8.E9): [`DLMF.AsymptoticApproximations.bessel_approximating_equation`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L114) (admitted)
- [2.8.E10](https://dlmf.nist.gov/2.8.E10): [`DLMF.AsymptoticApproximations.caseI_dominant_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L142) (proved)
- [2.8.E11](https://dlmf.nist.gov/2.8.E11): [`DLMF.AsymptoticApproximations.caseI_dominant_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L142) (proved)
- [2.8.E12](https://dlmf.nist.gov/2.8.E12): [`DLMF.AsymptoticApproximations.caseI_recessive_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L180) (proved)
- [2.8.E13](https://dlmf.nist.gov/2.8.E13): [`DLMF.AsymptoticApproximations.caseI_dominant_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L142) (proved); [`DLMF.AsymptoticApproximations.caseI_recessive_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L180) (proved)
- [2.8.E14](https://dlmf.nist.gov/2.8.E14): [`DLMF.AsymptoticApproximations.caseII_airy_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L218) (admitted)
- [2.8.E15](https://dlmf.nist.gov/2.8.E15): [`DLMF.AsymptoticApproximations.caseII_airy_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L218) (admitted)
- [2.8.E16](https://dlmf.nist.gov/2.8.E16): [`DLMF.AsymptoticApproximations.caseII_airy_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L218) (admitted)
- [2.8.E17](https://dlmf.nist.gov/2.8.E17): [`DLMF.AsymptoticApproximations.caseII_airy_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L218) (admitted)
- [2.8.E18](https://dlmf.nist.gov/2.8.E18): [`DLMF.AsymptoticApproximations.caseII_airy_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L218) (admitted)
- [2.8.E19](https://dlmf.nist.gov/2.8.E19): [`DLMF.AsymptoticApproximations.airyEnvCrit`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L106) (definition)
- [2.8.E20](https://dlmf.nist.gov/2.8.E20): [`DLMF.AsymptoticApproximations.envAi`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L112) (definition); [`DLMF.AsymptoticApproximations.envBi`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L120) (definition)
- [2.8.E21](https://dlmf.nist.gov/2.8.E21): [`DLMF.AsymptoticApproximations.envAi`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L112) (definition); [`DLMF.AsymptoticApproximations.envBi`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L120) (definition)
- [2.8.E22](https://dlmf.nist.gov/2.8.E22): [`DLMF.AsymptoticApproximations.caseII_airy_envelope`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L248) (admitted)
- [2.8.E23](https://dlmf.nist.gov/2.8.E23): [`DLMF.AsymptoticApproximations.caseII_airy_envelope`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L248) (admitted)
- [2.8.E24](https://dlmf.nist.gov/2.8.E24): [`DLMF.AsymptoticApproximations.caseIII_bessel_expansion_pos`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L277) (admitted)
- [2.8.E25](https://dlmf.nist.gov/2.8.E25): [`DLMF.AsymptoticApproximations.caseIII_bessel_expansion_pos`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L277) (admitted)
- [2.8.E26](https://dlmf.nist.gov/2.8.E26): [`DLMF.AsymptoticApproximations.caseIII_bessel_expansion_pos`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L277) (admitted)
- [2.8.E27](https://dlmf.nist.gov/2.8.E27): [`DLMF.AsymptoticApproximations.caseIII_bessel_expansion_pos`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L277) (admitted)
- [2.8.E28](https://dlmf.nist.gov/2.8.E28): [`DLMF.AsymptoticApproximations.caseIII_bessel_expansion_pos`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L277) (admitted)
- [2.8.E29](https://dlmf.nist.gov/2.8.E29): [`DLMF.AsymptoticApproximations.caseIII_bessel_expansion_neg`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L309) (admitted)
- [2.8.E30](https://dlmf.nist.gov/2.8.E30): [`DLMF.AsymptoticApproximations.caseIII_bessel_expansion_neg`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L309) (admitted)
- [2.8.E31](https://dlmf.nist.gov/2.8.E31): [`DLMF.AsymptoticApproximations.caseIII_bessel_expansion_neg`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L309) (admitted)
- [2.8.E32](https://dlmf.nist.gov/2.8.E32): [`DLMF.AsymptoticApproximations.besselEnvCrit`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L128) (definition)
- [2.8.E33](https://dlmf.nist.gov/2.8.E33): [`DLMF.AsymptoticApproximations.envJ`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L133) (definition); [`DLMF.AsymptoticApproximations.envY`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L140) (definition)
- [2.8.E34](https://dlmf.nist.gov/2.8.E34): [`DLMF.AsymptoticApproximations.envJ`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L133) (definition); [`DLMF.AsymptoticApproximations.envY`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L140) (definition)
- [2.8.E35](https://dlmf.nist.gov/2.8.E35): [`DLMF.AsymptoticApproximations.caseIII_bessel_envelope`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L340) (admitted)
- [2.8.E36](https://dlmf.nist.gov/2.8.E36): [`DLMF.AsymptoticApproximations.caseIII_bessel_envelope`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L340) (admitted)
- [2.8.i](https://dlmf.nist.gov/2.8.i) (prose): [`DLMF.AsymptoticApproximations.liouville_caseI`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L65) (proved)
- [2.8.ii](https://dlmf.nist.gov/2.8.ii) (prose): [`DLMF.AsymptoticApproximations.caseI_dominant_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L142) (proved); [`DLMF.AsymptoticApproximations.caseI_recessive_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L180) (proved)
- [2.8.iii](https://dlmf.nist.gov/2.8.iii) (prose): [`DLMF.AsymptoticApproximations.caseII_airy_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L218) (admitted)
- [2.8.iv](https://dlmf.nist.gov/2.8.iv) (prose): [`DLMF.AsymptoticApproximations.caseIII_bessel_expansion_pos`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L277) (admitted)
- [2.8.i](https://dlmf.nist.gov/2.8.i): [`DLMF.AsymptoticApproximations.liouville_caseI`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L65) (proved).
- [2.8.ii](https://dlmf.nist.gov/2.8.ii): [`DLMF.AsymptoticApproximations.caseI_dominant_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L142) (proved); [`DLMF.AsymptoticApproximations.caseI_recessive_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L180) (proved).
- [2.8.iii](https://dlmf.nist.gov/2.8.iii): [`DLMF.AsymptoticApproximations.caseII_airy_expansion`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L218) (admitted).
- [2.8.iv](https://dlmf.nist.gov/2.8.iv): [`DLMF.AsymptoticApproximations.caseIII_bessel_expansion_pos`](DLMF/AsymptoticApproximations/ODE/Parameter.lean#L277) (admitted).

## [§2.9 Difference Equations](https://dlmf.nist.gov/2.9)

- [2.9.E1](https://dlmf.nist.gov/2.9.E1): [`DLMF.AsymptoticApproximations.recurrence_eq_difference`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L35) (proved); [`DLMF.AsymptoticApproximations.recurrence_iff_difference`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L44) (proved)
- [2.9.E2](https://dlmf.nist.gov/2.9.E2): [`DLMF.AsymptoticApproximations.recurrence_eq_difference`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L35) (proved); [`DLMF.AsymptoticApproximations.recurrence_iff_difference`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L44) (proved)
- [2.9.E3](https://dlmf.nist.gov/2.9.E3): [`DLMF.AsymptoticApproximations.difference_distinct_roots_solution`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L52) (admitted)
- [2.9.E4](https://dlmf.nist.gov/2.9.E4): [`DLMF.AsymptoticApproximations.differenceCoeff`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L155) (definition); [`DLMF.AsymptoticApproximations.difference_distinct_roots_solution`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L52) (admitted)
- [2.9.E5](https://dlmf.nist.gov/2.9.E5): [`DLMF.AsymptoticApproximations.difference_distinct_roots_solution`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L52) (admitted)
- [2.9.E6](https://dlmf.nist.gov/2.9.E6): [`DLMF.AsymptoticApproximations.differenceExponent`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L149) (definition)
- [2.9.E7](https://dlmf.nist.gov/2.9.E7): [`DLMF.AsymptoticApproximations.differenceCoeff`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L155) (definition); [`DLMF.AsymptoticApproximations.IsDifferenceCoeffRel`](DLMF/AsymptoticApproximations/ODE/Defs.lean#L173) (definition)
- [2.9.E8](https://dlmf.nist.gov/2.9.E8): [`DLMF.AsymptoticApproximations.difference_distinct_roots_solution`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L52) (admitted)
- [2.9.E9](https://dlmf.nist.gov/2.9.E9): [`DLMF.AsymptoticApproximations.difference_coincident_sqrt`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L105) (admitted)
- [2.9.E10](https://dlmf.nist.gov/2.9.E10): [`DLMF.AsymptoticApproximations.difference_coincident_sqrt`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L105) (admitted)
- [2.9.E11](https://dlmf.nist.gov/2.9.E11): [`DLMF.AsymptoticApproximations.difference_coincident_power`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L124) (admitted)
- [2.9.E12](https://dlmf.nist.gov/2.9.E12): [`DLMF.AsymptoticApproximations.difference_coincident_power`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L124) (admitted); [`DLMF.AsymptoticApproximations.difference_coincident_power_int`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L141) (admitted)
- [2.9.E13](https://dlmf.nist.gov/2.9.E13): [`DLMF.AsymptoticApproximations.difference_coincident_log`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L156) (admitted)
- [2.9.E14](https://dlmf.nist.gov/2.9.E14): no statement (references only: the equation form for which Wong and Li (1992a) give analogous results)
- [2.9.i](https://dlmf.nist.gov/2.9.i) (prose): [`DLMF.AsymptoticApproximations.difference_distinct_roots_solution`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L52) (admitted); [`DLMF.AsymptoticApproximations.difference_distinct_roots_independent`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L67) (admitted); [`DLMF.AsymptoticApproximations.difference_recessive`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L83) (admitted)
- [2.9.ii](https://dlmf.nist.gov/2.9.ii) (prose): [`DLMF.AsymptoticApproximations.difference_coincident_sqrt`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L105) (admitted); [`DLMF.AsymptoticApproximations.difference_coincident_power`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L124) (admitted); [`DLMF.AsymptoticApproximations.difference_coincident_power_int`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L141) (admitted); [`DLMF.AsymptoticApproximations.difference_coincident_log`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L156) (admitted)
- [2.9.i](https://dlmf.nist.gov/2.9.i): [`DLMF.AsymptoticApproximations.difference_distinct_roots_independent`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L67) (admitted); [`DLMF.AsymptoticApproximations.difference_distinct_roots_solution`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L52) (admitted); [`DLMF.AsymptoticApproximations.difference_recessive`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L83) (admitted).
- [2.9.ii](https://dlmf.nist.gov/2.9.ii): [`DLMF.AsymptoticApproximations.difference_coincident_log`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L156) (admitted); [`DLMF.AsymptoticApproximations.difference_coincident_power`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L124) (admitted); [`DLMF.AsymptoticApproximations.difference_coincident_power_int`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L141) (admitted); [`DLMF.AsymptoticApproximations.difference_coincident_sqrt`](DLMF/AsymptoticApproximations/ODE/Difference.lean#L105) (admitted).

## [§2.10 Sums and Sequences](https://dlmf.nist.gov/2.10)

- [2.10.E1](https://dlmf.nist.gov/2.10.E1): [`DLMF.AsymptoticApproximations.euler_maclaurin`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L62) (proved)
- [2.10.E2](https://dlmf.nist.gov/2.10.E2): [`DLMF.AsymptoticApproximations.abel_plana`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L126) (admitted)
- [2.10.E3](https://dlmf.nist.gov/2.10.E3): [`DLMF.AsymptoticApproximations.jLogJSum`](DLMF/AsymptoticApproximations/Sums/Defs.lean#L37) (definition)
- [2.10.E4](https://dlmf.nist.gov/2.10.E4): [`DLMF.AsymptoticApproximations.jLogJSum_eq`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L155) (admitted); [`DLMF.AsymptoticApproximations.tendsto_jLogJSum_sub`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L174) (proved)
- [2.10.E5](https://dlmf.nist.gov/2.10.E5): [`DLMF.AsymptoticApproximations.jLogJRemainder`](DLMF/AsymptoticApproximations/Sums/Defs.lean#L41) (definition); [`DLMF.AsymptoticApproximations.jLogJSum_eq`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L155) (admitted)
- [2.10.E6](https://dlmf.nist.gov/2.10.E6): [`DLMF.AsymptoticApproximations.log_glaisherKinkelin_eq`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L189) (proved)
- [2.10.E7](https://dlmf.nist.gov/2.10.E7): [`DLMF.AsymptoticApproximations.powerSum_asymptotic`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L202) (admitted)
- [2.10.E8](https://dlmf.nist.gov/2.10.E8): [`DLMF.AsymptoticApproximations.harmonic_asymptotic`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L222) (admitted); Mathlib [`Real.tendsto_harmonic_sub_log`](DLMF/AsymptoticApproximations/Sums/MathlibCoverage.lean#L22) (upstream pointer)
- [2.10.E9](https://dlmf.nist.gov/2.10.E9): [`DLMF.AsymptoticApproximations.sum_by_parts`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L243) (proved); Mathlib [`Finset.sum_range_by_parts`](DLMF/AsymptoticApproximations/Sums/MathlibCoverage.lean#L19) (upstream pointer)
- [2.10.E10](https://dlmf.nist.gov/2.10.E10): [`DLMF.AsymptoticApproximations.partialSumFrom`](DLMF/AsymptoticApproximations/Sums/Defs.lean#L49) (definition); [`DLMF.AsymptoticApproximations.sum_by_parts`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L243) (proved)
- [2.10.E11](https://dlmf.nist.gov/2.10.E11): [`DLMF.AsymptoticApproximations.oscillatorySum`](DLMF/AsymptoticApproximations/Sums/Defs.lean#L53) (definition)
- [2.10.E12](https://dlmf.nist.gov/2.10.E12): [`DLMF.AsymptoticApproximations.norm_oscillatorySum_le`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L264) (proved); [`DLMF.AsymptoticApproximations.oscillatorySum_isBigO_trivial`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L273) (admitted)
- [2.10.E13](https://dlmf.nist.gov/2.10.E13): [`DLMF.AsymptoticApproximations.partialSumFrom_exp`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L282) (proved)
- [2.10.E14](https://dlmf.nist.gov/2.10.E14): [`DLMF.AsymptoticApproximations.oscillatorySum_eq`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L302) (proved)
- [2.10.E15](https://dlmf.nist.gov/2.10.E15): [`DLMF.AsymptoticApproximations.rpow_sub_rpow_succ`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L333) (admitted)
- [2.10.E16](https://dlmf.nist.gov/2.10.E16): [`DLMF.AsymptoticApproximations.oscillatorySum_recursive`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L342) (admitted)
- [2.10.E17](https://dlmf.nist.gov/2.10.E17): [`DLMF.AsymptoticApproximations.oscillatorySum_isBigO`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L353) (admitted)
- [2.10.E18](https://dlmf.nist.gov/2.10.E18): [`DLMF.AsymptoticApproximations.oscillatorySum_asymptotic`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L359) (admitted)
- [2.10.E19](https://dlmf.nist.gov/2.10.E19): [`DLMF.AsymptoticApproximations.genCoeff_zero_one_one`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L38) (proved); [`DLMF.AsymptoticApproximations.hypergeometric0F2OneOne_hasSum`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L59) (proved); [`DLMF.AsymptoticApproximations.genSeriesConvergesTo_0F2`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L71) (proved); [`DLMF.AsymptoticApproximations.hypergeometric0F2OneOne`](DLMF/AsymptoticApproximations/Sums/Defs.lean#L58) (definition)
- [2.10.E20](https://dlmf.nist.gov/2.10.E20): [`DLMF.AsymptoticApproximations.sum_0F2_eq_contourIntegral`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L78) (admitted)
- [2.10.E21](https://dlmf.nist.gov/2.10.E21): [`DLMF.AsymptoticApproximations.cot_div_two_I`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L87) (proved)
- [2.10.E22](https://dlmf.nist.gov/2.10.E22): [`DLMF.AsymptoticApproximations.sum_0F2_eq_real_integral_add`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L118) (admitted)
- [2.10.E23](https://dlmf.nist.gov/2.10.E23): [`DLMF.AsymptoticApproximations.hypergeometric0F2OneOne_eq_integrals`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L131) (admitted); [`DLMF.AsymptoticApproximations.hypergeometric0F2OneOne_sub_integral_isBigO`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L144) (admitted)
- [2.10.E24](https://dlmf.nist.gov/2.10.E24): [`DLMF.AsymptoticApproximations.hypergeometric0F2OneOne_isEquivalent`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L152) (admitted)
- [2.10.E25](https://dlmf.nist.gov/2.10.E25): [`DLMF.AsymptoticApproximations.laurent_expansion`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L162) (admitted)
- [2.10.E26](https://dlmf.nist.gov/2.10.E26): [`DLMF.AsymptoticApproximations.laurent_expansion`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L162) (admitted); [`DLMF.AsymptoticApproximations.laurentCoeff`](DLMF/AsymptoticApproximations/Sums/Defs.lean#L93) (definition)
- [2.10.E27](https://dlmf.nist.gov/2.10.E27): [`DLMF.AsymptoticApproximations.darboux`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L172) (admitted)
- [2.10.E28](https://dlmf.nist.gov/2.10.E28): [`DLMF.AsymptoticApproximations.darboux`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L172) (admitted)
- [2.10.E29](https://dlmf.nist.gov/2.10.E29): [`DLMF.AsymptoticApproximations.darboux`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L172) (admitted)
- [2.10.E30](https://dlmf.nist.gov/2.10.E30): [`DLMF.AsymptoticApproximations.darboux_singular`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L189) (admitted)
- [2.10.E31](https://dlmf.nist.gov/2.10.E31): [`DLMF.AsymptoticApproximations.darboux_smooth`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L205) (admitted)
- [2.10.E32](https://dlmf.nist.gov/2.10.E32): [`DLMF.AsymptoticApproximations.darboux_smooth_singular`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L218) (admitted)
- [2.10.E33](https://dlmf.nist.gov/2.10.E33): [`DLMF.AsymptoticApproximations.legendre_generating_cos`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L237) (proved)
- [2.10.E34](https://dlmf.nist.gov/2.10.E34): [`DLMF.AsymptoticApproximations.legendreComparison_hasSum`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L245) (admitted); [`DLMF.AsymptoticApproximations.legendreComparison`](DLMF/AsymptoticApproximations/Sums/Defs.lean#L99) (definition)
- [2.10.E35](https://dlmf.nist.gov/2.10.E35): [`DLMF.AsymptoticApproximations.legendreComparison_hasSum`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L245) (admitted)
- [2.10.E36](https://dlmf.nist.gov/2.10.E36): [`DLMF.AsymptoticApproximations.legendrePolyP_cos_asymptotic`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L256) (admitted)
- [2.10.i](https://dlmf.nist.gov/2.10.i) (prose): [`DLMF.AsymptoticApproximations.jLogJRemainder_bound`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L166) (admitted); [`DLMF.AsymptoticApproximations.powerSum_remainder_bound`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L210) (admitted); [`DLMF.AsymptoticApproximations.harmonic_remainder_bound`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L230) (admitted)
- [2.10.iv](https://dlmf.nist.gov/2.10.iv) (prose): [`DLMF.AsymptoticApproximations.darboux`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L172) (admitted); [`DLMF.AsymptoticApproximations.darboux_singular`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L189) (admitted); [`DLMF.AsymptoticApproximations.legendrePolyP_cos_asymptotic`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L256) (admitted)
- [2.10.i](https://dlmf.nist.gov/2.10.i): [`DLMF.AsymptoticApproximations.harmonic_remainder_bound`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L230) (admitted); [`DLMF.AsymptoticApproximations.jLogJRemainder_bound`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L166) (admitted); [`DLMF.AsymptoticApproximations.powerSum_remainder_bound`](DLMF/AsymptoticApproximations/Sums/EulerMaclaurin.lean#L210) (admitted).
- [2.10.iv](https://dlmf.nist.gov/2.10.iv): [`DLMF.AsymptoticApproximations.darboux`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L172) (admitted); [`DLMF.AsymptoticApproximations.darboux_singular`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L189) (admitted); [`DLMF.AsymptoticApproximations.legendrePolyP_cos_asymptotic`](DLMF/AsymptoticApproximations/Sums/Darboux.lean#L256) (admitted).

## [§2.11 Remainder Terms; Stokes Phenomenon](https://dlmf.nist.gov/2.11)

- [2.11.E1](https://dlmf.nist.gov/2.11.E1): [`DLMF.AsymptoticApproximations.cosRationalIntegral`](DLMF/AsymptoticApproximations/Remainders/Defs.lean#L36) (definition); [`DLMF.AsymptoticApproximations.cosRationalIntegral_asymptotic`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L41) (admitted)
- [2.11.E2](https://dlmf.nist.gov/2.11.E2): [`DLMF.AsymptoticApproximations.cosRationalCoeff`](DLMF/AsymptoticApproximations/Remainders/Defs.lean#L40) (definition); [`DLMF.AsymptoticApproximations.cosRationalIntegral_asymptotic`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L41) (admitted)
- [2.11.E3](https://dlmf.nist.gov/2.11.E3): [`DLMF.AsymptoticApproximations.cosRationalCoeff_explicit`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L50) (admitted)
- [2.11.E4](https://dlmf.nist.gov/2.11.E4): excluded: numerical
- [2.11.E5](https://dlmf.nist.gov/2.11.E5): [`DLMF.AsymptoticApproximations.genExpIntE_eq_integral`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L61) (proved)
- [2.11.E6](https://dlmf.nist.gov/2.11.E6): [`DLMF.AsymptoticApproximations.genExpIntE_asymptotic`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L75) (proved)
- [2.11.E7](https://dlmf.nist.gov/2.11.E7): [`DLMF.AsymptoticApproximations.genExpIntE_compound_asymptotic`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L84) (proved)
- [2.11.E8](https://dlmf.nist.gov/2.11.E8): [`DLMF.AsymptoticApproximations.terminant_eq_saddle_integral`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L136) (proved)
- [2.11.E9](https://dlmf.nist.gov/2.11.E9): [`DLMF.AsymptoticApproximations.inv_one_add_eq_sum`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L99) (proved)
- [2.11.E10](https://dlmf.nist.gov/2.11.E10): [`DLMF.AsymptoticApproximations.genExpIntE_eq_sum_add_terminant`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L110) (admitted)
- [2.11.E11](https://dlmf.nist.gov/2.11.E11): [`DLMF.AsymptoticApproximations.terminant_eq_integral`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L121) (proved)
- [2.11.E12](https://dlmf.nist.gov/2.11.E12): [`DLMF.AsymptoticApproximations.terminant_eq_saddle_integral`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L136) (proved)
- [2.11.E13](https://dlmf.nist.gov/2.11.E13): [`DLMF.AsymptoticApproximations.terminant_reexpansions`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L160) (admitted)
- [2.11.E14](https://dlmf.nist.gov/2.11.E14): [`DLMF.AsymptoticApproximations.stokesA2`](DLMF/AsymptoticApproximations/Remainders/Defs.lean#L55) (definition); [`DLMF.AsymptoticApproximations.terminant_reexpansions`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L160) (admitted)
- [2.11.E15](https://dlmf.nist.gov/2.11.E15): [`DLMF.AsymptoticApproximations.terminant_reexpansions`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L160) (admitted)
- [2.11.E16](https://dlmf.nist.gov/2.11.E16): [`DLMF.AsymptoticApproximations.stokesC`](DLMF/AsymptoticApproximations/Remainders/Defs.lean#L46) (definition); [`DLMF.AsymptoticApproximations.stokesC_sq`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L189) (proved); [`DLMF.AsymptoticApproximations.stokesC_continuous_tendsto`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L203) (admitted)
- [2.11.E17](https://dlmf.nist.gov/2.11.E17): [`DLMF.AsymptoticApproximations.stokesH`](DLMF/AsymptoticApproximations/Remainders/Defs.lean#L62) (definition); [`DLMF.AsymptoticApproximations.terminant_reexpansions`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L160) (admitted)
- [2.11.E18](https://dlmf.nist.gov/2.11.E18): [`DLMF.AsymptoticApproximations.stokesH_zero`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L210) (proved)
- [2.11.E19](https://dlmf.nist.gov/2.11.E19): [`DLMF.AsymptoticApproximations.rankOne_terminant_reexpansion`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L231) (admitted)
- [2.11.E20](https://dlmf.nist.gov/2.11.E20): [`DLMF.AsymptoticApproximations.rankOne_terminant_reexpansion`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L231) (admitted)
- [2.11.E21](https://dlmf.nist.gov/2.11.E21): [`DLMF.AsymptoticApproximations.rankOne_terminant_reexpansion`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L231) (admitted)
- [2.11.E22](https://dlmf.nist.gov/2.11.E22): [`DLMF.AsymptoticApproximations.rankOne_terminant_reexpansion`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L231) (admitted)
- [2.11.E23](https://dlmf.nist.gov/2.11.E23): [`DLMF.AsymptoticApproximations.rankOne_terminant_reexpansion`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L231) (admitted)
- [2.11.E24](https://dlmf.nist.gov/2.11.E24): [`DLMF.AsymptoticApproximations.expIntE1_asymptotic`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L281) (proved)
- [2.11.E25](https://dlmf.nist.gov/2.11.E25): excluded: numerical
- [2.11.E26](https://dlmf.nist.gov/2.11.E26): excluded: numerical
- [2.11.E27](https://dlmf.nist.gov/2.11.E27): excluded: numerical
- [2.11.E28](https://dlmf.nist.gov/2.11.E28): excluded: numerical
- [2.11.E29](https://dlmf.nist.gov/2.11.E29): [`DLMF.AsymptoticApproximations.whittakerW_asymptotic`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L306) (proved)
- [2.11.E30](https://dlmf.nist.gov/2.11.E30): [`DLMF.AsymptoticApproximations.whittakerTerm`](DLMF/AsymptoticApproximations/Remainders/Defs.lean#L70) (definition); [`DLMF.AsymptoticApproximations.whittakerW_asymptotic`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L306) (proved)
- [2.11.E31](https://dlmf.nist.gov/2.11.E31): excluded: numerical
- [2.11.E32](https://dlmf.nist.gov/2.11.E32): [`DLMF.AsymptoticApproximations.levinTransform`](DLMF/AsymptoticApproximations/Remainders/Defs.lean#L78) (definition)
- [2.11.iii](https://dlmf.nist.gov/2.11.iii) (prose): [`DLMF.AsymptoticApproximations.terminant_reexpansions`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L160) (admitted)
- [2.11.iv](https://dlmf.nist.gov/2.11.iv) (prose): [`DLMF.AsymptoticApproximations.stokesC_re_sign`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L221) (admitted)
- [2.11.v](https://dlmf.nist.gov/2.11.v) (prose): [`DLMF.AsymptoticApproximations.rankOne_terminant_reexpansion`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L231) (admitted)
- [2.11.iii](https://dlmf.nist.gov/2.11.iii): [`DLMF.AsymptoticApproximations.terminant_reexpansions`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L160) (admitted).
- [2.11.iv](https://dlmf.nist.gov/2.11.iv): [`DLMF.AsymptoticApproximations.stokesC_re_sign`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L221) (admitted).
- [2.11.v](https://dlmf.nist.gov/2.11.v): [`DLMF.AsymptoticApproximations.rankOne_terminant_reexpansion`](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L231) (admitted).
### Prose, informal and excluded items (part g2b)

- §2.6(i)–(ii): the Stieltjes-transform discussion is covered by the numbered formulas; the
  remark on more detailed discussion (2.6.31 and the following references) is excluded:
  informal. §2.6(iii) (convolutions on `(0, ∞)`) is tagged `2.6.iii`. §2.6(iv) remarks on
  regularization (Gel'fand–Shilov, Jones) are references only beyond 2.6.58–2.6.62.
- §2.7(i)–(iv): the classification and existence statements are tagged `2.7.i`–`2.7.iv`;
  remarks on numerically satisfactory pairs beyond the example 2.7.35–2.7.37 and the
  references (Olver, Wasow, Olde Daalhuis–Olver) are excluded: informal.
- §2.8(i)–(iv): tagged `2.8.i`–`2.8.iv`. §2.8(v) (multiple and fractional turning points) and
  §2.8(vi) (other approximations) are no statement (references only).
- §2.9(i)–(ii): tagged `2.9.i`, `2.9.ii` (recessive/dominant solutions, independence);
  §2.9(iii) is no statement (references only). The remark "for asymptotic expansions in
  inverse factorial series see …" is references only.
- §2.10(i): the sign and bound statements for `R_m(n)` and for 2.10.7–2.10.8 are tagged
  `2.10.i`; extensions (Sidi, Weniger, Elliott) are references only. §2.10(ii)–(iii) remarks
  ("useful approximation when `α > 0`", generalizations) are excluded: informal. §2.10(iv):
  conditions (a)–(c), (b′) are formalized as hypotheses (`2.10.iv` tag); uniform expansions
  for coalescing singularities (Wong–Zhao) are references only.
- §2.11(i): the cautionary discussion, including the remark that 2.11.2 is more accurate for
  `I(m) - ½πe^{-m}`, is excluded: informal; 2.11.4 is excluded: numerical. §2.11(iii): the
  "conjugate result" for `-3π + δ ≤ ph z ≤ π - δ` is excluded: informal. §2.11(iv): the
  half-plane location of `c(θ)` is tagged `2.11.iv`; the descriptions of the erfc transition,
  Figure 2.11.1, Stokes lines and higher-order Stokes phenomena are excluded: informal or
  graphical. §2.11(v): tagged `2.11.v`; hyperasymptotics and Borel-transform remarks are
  references only. §2.11(vi): 2.11.25–2.11.28, 2.11.31 and Table 2.11.1 are excluded:
  numerical; the definition 2.11.32 (`levinTransform`) is a definition only.

### Validation (part g2b)

- `lake build` of the 15 modules succeeds (log: 0 errors; the only warnings in these files are
  `declaration uses 'sorry'`, 83 of them).
- Each file passes `lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false` with no
  errors and no warnings other than `sorry`.
- `#print axioms` on all 49 proved theorems: `[propext, Classical.choice, Quot.sound]`, except
  `kPlusPairing_powKernel_conv_log` (also `sorryAx`, via the admitted 2.6.40 identity). No
  `axiom`, `native_decide` or `sorry` in definitions.
- Numerical and symbolic checks (mpmath, sympy): 2.6.7 (errors `≪ x^{-n-1/3}`), 2.6.40,
  2.6.45, 2.6.47 (`n = 1, 2`), 2.6.51, 2.6.53; the recursions 2.7.11 and 2.9.7 (residuals zero);
  2.10.4 (sign and bound of `R_m`), 2.10.6, 2.10.7–2.10.8 with the §2.10(i) remainder bounds,
  2.10.18, 2.10.24, 2.10.35–2.10.36 (`α = 0.9, 2.5`); 2.11.3 (sympy), 2.11.10,
  2.11.13–2.11.14 (error `∼ ρ^{-2}`), 2.11.15 and 2.11.18 (`θ < π`); `c(θ)`: the quotient in
  `stokesC` avoids `(-∞, 0]` on `(-π, 3π)` and `ℜc(θ)` changes sign at `θ = π`.
- Lines ≤ 100 characters; every declaration has a docstring citing its DLMF equation and
  domain/branch.
