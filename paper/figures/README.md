# Active-block arrangement figure

Adapted from the residual-slt-guide visual explainer's block chains (01-puzzle) and inactive-group indicators (09-inactive-groups). The manuscript figure shows all three distinct depth-five cubic cases, with notation matching Table 1.

- Endpoint, e1: inactive lengths (0,4), local pair (13/12,1).
- One position inward, e2: lengths (1,3), pair (7/6,2).
- Center, e3: lengths (2,2), pair (7/6,1).

Every chain computes x+x^3. Boxes denote full residual blocks and show raw weights; filled black boxes are active. Brackets indicate consecutive inactive groups. No color carries information. The vector PDF is used in the manuscript; SVG and PNG versions are also supplied.

Run `python3 make_arrangements.py` with matplotlib installed. The generator verifies the labels using exact fractional evaluation of the manuscript's group rule. This is a consistency check, not an experiment or a new proof.
