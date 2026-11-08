# A Needle in Five Tiny Haystacks: Local Learning Coefficients of Scalar ResNets

Bobby Faber, Independent. 7 November 2026.

- `main.pdf`: compiled manuscript.
- `main.tex` and `references.bib`: editable sources.
- `figures/`: monochrome arrangement figure and its Python generator.
- `formalization_status.md`: current certified statements and exact assumptions.
- `checks/`: release build, focused audit, and library audit/check logs.

Public proof repository: https://github.com/bubskee/residual-slt-in-a-haystack

The three theorems give the identity-target phase transition, local arrangement pairs, and complete fibers and global selection for arbitrary active counts. The global theorem includes exact raw-fiber sizes. Lean certifies the fiber results and local/global Laplace orders under the paper's sparse Gram assumption.

All three theorems are formalized in Lean 4; `formalization_status.md` records the certified statements and their exact assumptions.

## Compile

From `paper/`, run `tectonic --keep-logs main.tex` (verified with Tectonic 0.17.0), or `latexmk -pdf main.tex` with a standard LaTeX installation and BibTeX. The vector figure is included.

## Reproduce the formal checks

Clone the public proof repository and follow [formalization_status.md](formalization_status.md). The manuscript-only bundle includes the focused audit and logs; the full repository includes the pinned Lean source and library checks.

## Regenerate the figure

With Python and matplotlib installed, run `python3 figures/make_arrangements.py`. The generator checks the three local pairs using exact fractions and writes PDF, SVG, and PNG versions. Black boxes mark active blocks; brackets identify inactive groups. The pairs agree with Table 1.
