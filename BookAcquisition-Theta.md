# Theta functions from Igusa, Mumford and Beals–Wong

## Sources and selection

The PDFs are read from `../lean-CKMA/References`; the formalization remains in
`DLMF/RiemannTheta`, in the namespace `DLMF.RiemannTheta`. The seven books listed below
were converted to searchable text, and their contents and relevant theta sections were
compared with the existing DLMF, Mathlib and pinned TauCeti coverage. This is a selection
of basic theory, not a theorem-by-theorem acquisition of all seven books. Source hashes,
the declaration inventory and validation are recorded in
`reports/ThetaBooksValidation.json`.

- **Igusa, Theta Functions (1972).** Chapters I–II develop analytic theta functions,
  automorphy and theta spaces; Chapter IV, §1 develops addition formulas. Chapter V,
  §6, pp. 209–211, develops even and odd characteristics. The additions use the
  principal-polarization case with integral order. General polarizations, modular forms,
  and the algebraic classification of abelian varieties remain outside this selection.
- **Mumford, Tata Lectures on Theta I (2007 reprint).** Chapter I, §3 motivates the
  translation operators and their Heisenberg relation. Chapter II, Definition 1.2,
  pp. 122–123, supplies the spaces of theta functions of weight/order `N`.
  Proposition 1.3, pp. 124–125, supplies the functions `θ[a/N;0](Nz|NΩ)`.
  Chapter II, §3, pp. 168–170, supplies the even/odd half-characteristic counts.
  The functions and their automorphy are proved here; Proposition 1.3's basis and
  dimension assertions are not yet proved.
- **Mumford, Tata Lectures on Theta II (2007 reprint).** Chapter IIIa, §6 gives the
  geometric setting for theta characteristics and vanishing. Chapter IIIb, §2 gives
  another analytic normalization and the setting for Fay identities. The new parity
  and odd-constant vanishing results provide analytic prerequisites. The geometric
  Riemann singularity theorem, hyperelliptic theta formulas and Fay identities are
  not claimed as formalized.
- **Beals–Wong, Explorations in Complex Functions (2020).** Sections 14.2–14.3 give
  theta functions and their use in constructing elliptic functions. The new
  equal-order quotient theorem proves meromorphy in genus one and all periods
  `m + nτ`. It avoids an unjustified exact pole-order assertion when numerator and
  denominator divisors cancel; see `ERRATA-BealsWong.md`.
- **Beals–Wong, More Explorations in Complex Functions (2023).** Section 11.3,
  pp. 272–273, uses the negative-real-part normalization. The existing
  `riemannThetaBig` is retained, with new domain, parity, periodicity and entire
  differentiability theorems. Two displayed formulas require the corrections
  documented in `ERRATA-BealsWong.md`.
- **Beals–Wong, Special Functions: A Graduate Text (2010).** Sections 11.4–11.5
  cover classical theta functions, Jacobi normalization and integration. These
  substantially overlap the project's existing Theta, JacobiElliptic and
  EllipticIntegrals areas; no second set of definitions is introduced.
- **Beals–Wong, Special Functions and Orthogonal Polynomials (2015).** The elliptic
  and theta material was checked for overlap with the existing named functions,
  transformations and integral modules. The higher-dimensional books above supply
  the main additional basic material selected here.

## Mathematical additions

The eight substantive modules add **54 proved theorems and eight definitions**. A ninth
module relocates seven existing theorems and one definition into the foundational layer.
Every new result has an axiom audit without `sorryAx`.

- `Basic/Analytic.lean` proves joint entire analyticity and differentiability in the
  argument vector for theta functions and theta functions with real characteristics.
  It includes the empty index type. It reuses TauCeti's Osgood lemma
  `ContinuousOn.analyticOnNhd_of_differentiableAt_update`, together with the existing
  continuity and coordinate differentiability proofs.
- `Basic/Periodicity.lean` contains the existing parity and automorphy proofs, with
  their public names, tagged statements, docstrings and mathematical bodies preserved.
  The `Symmetry` module remains an import-compatible umbrella. This gives the new
  foundational definitions access to the laws without importing theorem-layer files.
- `Basic/Sections.lean` defines `thetaAutomorphyFactor` and the complex submodule
  `thetaSectionSpace N Ω` of entire functions with integer periods and the order-`N`
  multiplier under `Ωm`. It proves the multiplier cocycle, products adding orders,
  powers multiplying orders, constants at order zero, and membership of the canonical
  theta function at order one. Equal-order quotients are lattice periodic.
- `Basic/HigherOrder.lean` defines `thetaOfOrder N a z Ω = θ[a/N;0](Nz|NΩ)`.
  For `N > 0` and a Riemann matrix, it is entire and belongs to the order-`N` space.
  Labels are periodic modulo `N`, order one recovers theta, and every second-order
  function is even. Matrix scaling and both argument translation laws are proved.
- `Basic/AlternativeNormalization.lean` treats
  `Θ(φ|B) = θ(φ/(2πi)|B/(2πi))`. A symmetric `B` with negative definite real part
  gives a Riemann matrix after division by `2πi`. The full translation law is
  `Θ(φ + 2πim + Bn|B) = exp(-nBn/2 - nφ) Θ(φ|B)`.
- `CharacteristicParity.lean` defines the characteristic sign and the finite even/odd
  sets. Their counts are `(4^g + 2^g)/2` and `(4^g - 2^g)/2`. The proof includes
  genus zero, where the counts are one and zero. The sign controls theta parity,
  and every odd theta constant vanishes, including for totalized matrix parameters.
- `HigherOrderAddition.lean` derives
  `θ(z+w)θ(z-w) = Σ_a Θ₂,a(z)Θ₂,a(w)` over binary vector labels from the existing
  proved characteristic addition formula. It also proves the square specialization
  and membership of the symmetric translated product in the order-two space.
- `Translations.lean` defines rational and compensated period-matrix translations.
  It proves the Heisenberg commutation relation with scalar `exp(2πi p·q/N)`, that
  this scalar is an `N`-th root of unity for positive `N`, and that labels divisible
  by `N` act trivially on order-`N` sections. The operators act on arbitrary functions;
  preservation of the section space and a group representation are not asserted here.
- `EllipticQuotients.lean` proves that a quotient of two equal-order genus-one theta
  sections is meromorphic and periodic by every `m + nτ`. If `Im τ > 0`, these give
  the usual two independent periods. The result permits zero sections and cancellation;
  it makes no exact divisor-degree claim.

## Conventions and remaining scope

The existing theta series, characteristic functions and `riemannThetaBig` definition
bodies are unchanged. The new higher-order definition is total at `N = 0`, but its
usual convergent-function assertions assume `N > 0`. The section-space definition
does not require positivity or symmetry; these enter the theorems that construct
sections from convergent theta series. Period identities can hold at totalized
denominator zeros, while meromorphy is a statement about local germs.

The addition proofs reuse the already proved `riemannThetaChar_mul_addition`.
Other pre-existing targets in `Products` and `Modular` remain admitted; none is an
axiom dependency of these additions. No new admission or axiom is introduced.

Further substantial topics are the `N^g` basis theorem, preservation and representation
theory for the theta translation operators, arbitrary polarization types, Riemann's
vanishing/singularity theorems, Thomae formulas, and Fay identities. These require
additional analytic, line-bundle or Riemann-surface infrastructure and are not covered
by the elementary results above.

## Validation

The ordinary whole-project build, the targeted build of all twelve affected modules
and both entry modules, and twelve direct source checks pass. The direct checks treat
warnings as errors. All 62 new declarations and all eight relocated public declarations
have only standard Lean axioms. Import and file-length surveys pass, with no new
two-way area pairs, foundational closure violations, missing imports or file cycles.
The detailed inventory and final source hashes are in `reports/ThetaBooksValidation.json`.
