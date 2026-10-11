# Disproof of Conjecture 00000004215

An explicit complex has ten vertices, the complete one-skeleton and 36 listed triangles. Integer boundary certificates prove it is a two-dimensional spanning tree. For the actual up-down Laplacian L=A Aᵀ, explicit integer vectors b,w,c satisfy b=11c, Lw=11b, wᵀL=121cᵀ, and wᵀb=4081, which is nonzero modulo 121. Thus [b] is nonzero and killed by 11 in both the Laplacian cokernel and the first critical group. The prime 11 exceeds the vertex count 10.

## Scope

Uses the standard integer up-down Laplacian on edges and the conventional simplicial spanning-tree definition allowing finite H1 torsion, as specified in the cited primary reference. The ambient complex is the complete two-skeleton on ten vertices. The paper distinguishes this from the total Hodge Laplacian. A counterexample to the universal prime bound suffices; no claim about a corrected bound or lens-space attainment is made.

## Formalization

Lean constructs actual boundary matrices from the listed vertices, edges and oriented triangles. It checks full skeleton enumeration, face distinctness and downward closure, and all literal integer matrix certificates in its kernel. Algebraic extension to Q proves rational first homology vanishes; the left inverse up to 11 proves integral top homology vanishes. It constructs the cycle lattice and actual quotient groups, proves the witness class nonzero using the modulus-121 detector, and proves it is killed by 11. Both the critical-group and full matrix-cokernel conclusions are formalized. Discovery floats are not trusted; fresh Lean builds and an independent exact Python verifier check the fixed certificates.

## Reproduction

In `lean/`: `lake exe cache get`, `lake build`, and
`lake env lean -DwarningAsError=true Main.lean`.
Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`
are pinned. The project, including `Main/Certificate.lean`, is freshly built.
Run `python verify.py` for independent exact arithmetic using the standard
library only. Optional `python discovery.py` reproduces the basis-exchange
search and requires NumPy (`python -m pip install numpy`). Only discovery
uses floating point; all accepted certificates are exact and checked by Lean.
Run `tectonic main.tex` for the PDF.

`SOURCE.md` preserves the exact bilingual source; `verification/` records
provenance, actual build and script logs, hashes and review. No independent
reviewer or subagent was used; review was an adversarial author self-review.
