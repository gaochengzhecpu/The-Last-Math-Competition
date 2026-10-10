# Proof of Conjecture 00000006322

For every square matrix of positive size n over any field with 2 nonzero, derive the full 2^n-term sign-sum identity for the actual permanent. Global sign reversal is a fixed-point-free involution with equal paired summands. Fixing one sign leaves exactly 2^(n-1) terms and normalization 2^(-(n-1)), proving the pairing and conversion assertions.

## Scope

The result is the classical Glynn sign-sum formula, with a complete derivation and general Lean proof. It applies in particular over the rationals, reals and complex numbers, for every n>=1. The count is the number of indexed terms in this formula, not an algorithmic lower bound or an assertion that every summand is nonzero. The empty matrix and characteristic-two division are outside the pairing formula and are explicitly distinguished.

## Formalization

Lean expands the actual product of column sums, proves cancellation of every nonbijective row-choice function by a single-coordinate flip, and identifies surviving bijections with permutations in Matrix.permanent. It proves global sign reversal is a free involution, paired terms are equal, the two half-sums coincide, and the chosen half has exactly 2^(n-1) elements. Field cancellation gives the exact normalization. The final pairing_reduction theorem combines these claims for arbitrary finite positive dimension; sign_injective validates the Boolean sign encoding.

## Reproduction

In `lean/`, run `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`
are pinned in public-Git project metadata. Only verified official dependency
artifacts are reused; the submitted project is freshly rebuilt.
Run `tectonic main.tex` for the PDF. No auxiliary computation is required.

`SOURCE.md` preserves the exact bilingual source. `verification/` contains
provenance, actual build logs, hashes and review records. The author performed
a separate adversarial self-review; no independent reviewer or subagent was used.
