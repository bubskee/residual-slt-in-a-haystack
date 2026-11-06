# Learning Coefficients and Active-Block Arrangements in Scalar Residual Networks

Bobby Faber, Independent. 6 November 2026.

- `main.pdf`: compiled manuscript.
- `main.tex` and `references.bib`: editable sources.
- `figures/`: monochrome arrangement figure and its Python generator.
- `formalization_status.md`: current certified statements and exact assumptions.
- `checks/`: release build, focused audit, and library audit/check logs.

Public proof repository: https://github.com/bubskee/residual-slt-in-a-haystack

The three theorems give the identity-target phase transition, local arrangement pairs, and complete fibers and global selection for arbitrary active counts. The global theorem includes exact raw-fiber sizes. Lean certifies the fiber results and local/global Laplace orders under the paper's sparse Gram assumption.

Formal verification and extensions are ongoing. A growing subset of the results has been formalized in Lean 4; the repository documents the currently certified statements and their assumptions.

## Compile

From `paper/`, run `tectonic --keep-logs main.tex` (verified with Tectonic 0.17.0), or `latexmk -pdf main.tex` with a standard LaTeX installation and BibTeX. The vector figure is included.

## Reproduce the formal checks

Clone the public proof repository and follow [formalization_status.md](formalization_status.md). The manuscript-only bundle includes the focused audit and logs; the full repository includes the pinned Lean source and library checks.

## Regenerate the figure

With Python and matplotlib installed, run `python3 figures/make_arrangements.py`. The generator checks the three local pairs using exact fractions and writes PDF, SVG, and PNG versions. Black boxes mark active blocks; brackets identify inactive groups. The pairs agree with Table 1.
