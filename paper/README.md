# Learning Coefficients and Active-Block Arrangements in Scalar Residual Networks

Bobby Faber, Independent. 5 November 2026.

- `main.pdf`: compiled manuscript.
- `main.tex` and `references.bib`: editable manuscript sources.
- `figures/`: monochrome arrangement figure and its Python generator.
- `formalization_status.md`: exact formal hypotheses and coverage.
- `checks/`: focused audit source and release build/audit logs.

Public proof repository: https://github.com/bubskee/residual-slt-in-a-haystack

## Compile the manuscript

From `paper/`, run `tectonic --keep-logs main.tex` (verified with Tectonic 0.17.0), or use `latexmk -pdf main.tex` with a standard LaTeX installation and BibTeX. The included vector figure is ready to use; regenerating it is optional.

## Regenerate the figure

Install Python and matplotlib, then run `python3 figures/make_arrangements.py`. The generator checks all three local pairs using exact fractions and writes PDF, SVG, and PNG versions. Boxes contain raw weights; black means active, and brackets identify inactive groups. The pairs agree with Table 1.

## Reproduce the formal audit

Clone the public proof repository and follow `formalization_status.md`. The manuscript-only bundle contains the audit and logs; the repository also contains the pinned proof source. All theorem statements and mathematical proof arguments are unchanged by the final editorial pass.
