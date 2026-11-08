# Residual SLT in a Haystack

**A Needle in Five Haystacks: Local Learning Coefficients of a Scalar ResNet**  
Bobby Faber, Independent. 6 November 2026.

[Read the paper](paper/main.pdf) · [LaTeX source](paper/main.tex) · [Formal coverage](paper/formalization_status.md)

Exact learning coefficients for scalar, bias-free polynomial residual networks in raw weights. Active blocks separate inactive groups, so different realizations of the same function can have different local exponents or multiplicities. The three main theorems give the identity-target transition, local arrangement pairs, and complete fibers and global selection for every active count.

For a target with `k` active blocks at depth `L`, the raw fiber has `choose(L,k)` points for odd degree and `2^k * choose(L,k)` for even degree. Its global pair is `(k/2 + A_r(L-k), M_r(L-k))`; local pairs depend on the individual inactive-group lengths. Repeated active coefficients and all realizable signs are included.

Formal verification and extensions are ongoing. A growing subset of the results has been formalized in Lean 4; the repository documents the currently certified statements and their assumptions.

The current unified Lean certificate proves the complete fibers, exact counts, local arrangement pairs, and full-space global pairs under the sparse Gram and prior assumptions in the paper. Multiplicity means the logarithmic power in two-sided Laplace bounds. See [formal coverage](paper/formalization_status.md) for exact hypotheses and the correspondence with the paper.

## Reproduce the Lean checks

Install [elan](https://github.com/leanprover/elan), then:

```sh
git clone https://github.com/bubskee/residual-slt-in-a-haystack.git
cd residual-slt-in-a-haystack
git checkout b08b1a334abac97cbdf754ba14eacee82e10be70
cd lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true -DautoImplicit=false ../paper/checks/NetworkAudit.lean
lake env lean -DwarningAsError=true -DautoImplicit=false CheckUnifiedNetworkCertificate.lean
```

Lean `v4.35.0` and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` are pinned. The reproducibility snapshot [b08b1a334abac97cbdf754ba14eacee82e10be70](https://github.com/bubskee/residual-slt-in-a-haystack/tree/b08b1a334abac97cbdf754ba14eacee82e10be70) contains both the proof source and the focused audit. Its Lean source is unchanged from `3aa873960d83313e44d966ebc124655e87aa0982`. The release build, focused audit, and all 48 library audit/check files pass; logs and full rerun commands are linked in the coverage statement.

## Build the paper

```sh
cd paper
tectonic --keep-logs main.tex
```

The vector figure is included. Its optional Python generator requires matplotlib; see [figure documentation](paper/figures/README.md).

## Assistance

Following the disclosure recommendation of the [Leiden Declaration on Artificial Intelligence and Mathematics](https://doi.org/10.5281/zenodo.20302944), the manuscript records substantial AI assistance. Astra and Opus 5.5 assisted with writing, proof development, and Lean formalization. Fable 5.1 provided adversarial review and attempted to find errors in the arguments. The author retains responsibility for the results, arguments, and citations.

The author thanks BlueDot Impact for financial support.
