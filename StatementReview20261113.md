# Statements requiring review after the 2026-11-13 proof round

The first two repairs are applied with user approval and complete proofs. The patch
`reports/DLMFStatementCorrections20261113.patch` is retained as an applied record.
The six remaining branch and domain issues are unchanged in the library; no replacement
statement has been proposed for them.

## Two precise transcription repairs with checked proofs

- **Inverse-hyperbolic-sine continued fraction, DLMF 4.39.2.** In
  `DLMF/Elementary/Hyperbolic/Integrals.lean`, the second factor
  `(2*((n+1)/2):ℂ)` performs division in the complex numbers. The preceding factor
  performs natural-number division. Replacing the second factor by
  `((2*((n+1)/2):ℕ):ℂ)` makes both factors use natural-number division, giving the
  intended repeated coefficients `2, 2, 12, 12, …`. The uncorrected second coefficient
  instead evaluates to `3`. The proof of the corrected fraction, on the original
  principal domain, is saved as
  `DLMF.Elementary.ArcsineContinuedFraction.hasContinuedFraction_arcsinh`.
  `scripts/CheckDLMFArcsinhStatement.lean` checks the exact coefficient discrepancy and
  the finite-convergent expansion. That script does not claim a nonconvergence theorem
  for the incorrect infinite fraction. Source: [DLMF 4.39.2](https://dlmf.nist.gov/4.39.E2).
- **Spherical Carlson integral, DLMF 19.23.9.** In
  `DLMF/EllipticIntegrals/SymmetricIntegrals.lean`, the denominator needs parentheses:
  `/ (∏ j, Gamma (b j : ℂ)) * integral`. Without them the product binder captures the
  integral as well. At `a = 0`, with every `b j = z j = 1`, the left side is `1`,
  while the literal uncorrected right side is `4096`. The independent Lean counterexample
  is `scripts/CheckDLMFSphericalStatement.lean`; it computes the angular moment `1/8`
  without using an admitted sphere formula. The corrected identity has a checked proof
  for every permutation and all its original parameter hypotheses. Source:
  [DLMF 19.23.9](https://dlmf.nist.gov/19.23.E9).

Both corrected production theorems and both certificate scripts use only `propext`,
`Classical.choice` and `Quot.sound` in their checked axiom dependencies. The patch changes
no function definition or parameter hypothesis. Both repairs have been applied with user approval.

## Rhombic-lattice monotonicity: mathematical review needed

`DLMF.Weierstrass.rhombic_e_one_monotone`, in `DLMF/Weierstrass/SpecialLattices.lean`, follows the
monotonicity sentence in [DLMF 23.5(iv)](https://dlmf.nist.gov/23.5.iv). Numerical interval
evidence suggests that sentence is false on the full stated domain. With the real
half-period equal to `1`, and the other half-period equal to `1/2 + i b`, take
`b₁ = 1/5`, `b₂ = 1/10`: the required comparison of the imaginary parts of `e₃` holds,
while the asserted comparison of `e₁` is reversed.

The script `scripts/check_rhombic_numerical_evidence.py` evaluates the project's proved
theta formulas, enclosing finite sums with 60-digit interval arithmetic and bounding the
tails geometrically. Its saved output is
`reports/DLMF-rhombic-numerical-evidence-20261113.txt`. This is numerical evidence,
not a Lean counterexample. Replacing the comparison by `b₁ < b₂` looks like a possible
source correction; a restricted aspect-ratio domain is another possibility. Neither
candidate has been proved sufficient, so no replacement statement is proposed here.

## Complex quadratic Landen transformations: branch review needed

Five admissions in `EllipticIntegrals/SymmetricQuadratic.lean` appear to lack branch
conditions compatible with the independently selected principal square roots:
`symmetricEllipticRF_sq_landen`, `symmetricEllipticRD_sq_landen`,
`symmetricEllipticRJ_sq_landen`, `symmetricEllipticRG_sq_landen`, and
`symmetricEllipticRJ_zero_sq`.

A shared numerical witness has `x = 1/5 - 12i/5`, `y = 1/2 + 7i`, `z = 2 + 2i`.
For the general RJ identity take `p = 3/2 - i`; for the zero-node RJ identity take
`p = z` and the negative sign. The transformed arguments can leave the right half-plane,
and the principal-root identities give differing values. Swapping the sign of the
product square root only exchanges the transformed arguments and cannot fix the RF
identity, which is symmetric in those arguments.

The reproducer is `scripts/check_symmetric_landen_numerical_evidence.py`, with output
`reports/DLMF-symmetric-landen-numerical-evidence-20261113.txt`. These are high-precision
numerical evaluations, not Lean counterexamples. The source domain is
[DLMF 19.22](https://dlmf.nist.gov/19.22). Positive-real inputs or a suitable analytic
continuation condition may give correct scopes, but sufficiency remains unproved.
No weakening or definition change has been made.
