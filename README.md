# Residual SLT in a Haystack

**Learning Coefficients and Active-Block Arrangements in Scalar Residual Networks**  
Bobby Faber, Independent. 5 November 2026.

[Read the paper](paper/main.pdf) · [LaTeX source](paper/main.tex) · [Formal coverage](paper/formalization_status.md)

Exact local learning coefficients for scalar, bias-free polynomial residual networks in raw weights. Active blocks separate inactive groups; different placements can represent the same function while having different local exponents or multiplicities. The paper has three main theorems: the identity-target transition, the local arrangement theorem, and global selection for one or two active blocks.

## Reproduce the Lean checks

Install [elan](https://github.com/leanprover/elan), then:

```sh
git clone https://github.com/bubskee/residual-slt-in-a-haystack.git
cd residual-slt-in-a-haystack/lean
lake exe cache get
lake build
lake env lean -DwarningAsError=true -DautoImplicit=false ../paper/checks/IdentityAudit.lean
```

Lean `v4.35.0` and mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` are pinned. The audited proof source is commit `dfd9f7ee8c4338256a7cb7426ceaae7a038fbf00`; the manuscript commit adds the paper and focused audit record without changing any file under `lean/`.

Lean certifies the identity-target integrability thresholds and boundary divergence under the explicit contiguous feature-Gram and bounded-positive-prior assumptions. Multiplicities, Laplace asymptotics, the local arrangement theorem, and global selection have paper proofs only. See [the coverage statement](paper/formalization_status.md) for the exact hypothesis difference between the formal and paper results.

## Build the paper

```sh
cd paper
tectonic --keep-logs main.tex
```

The vector figure is included. Its optional Python generator requires matplotlib; see [figure documentation](paper/figures/README.md).

## Assistance

Following the disclosure recommendation of the [Leiden Declaration on Artificial Intelligence and Mathematics](https://doi.org/10.5281/zenodo.20302944), the manuscript records substantial AI assistance. Astra and Opus 5.5 assisted with writing, proof development, and Lean formalization. Fable 5.1 provided adversarial review and attempted to find errors in the arguments. The author retains responsibility for the results, arguments, and citations.

The author thanks BlueDot Impact for financial support.
