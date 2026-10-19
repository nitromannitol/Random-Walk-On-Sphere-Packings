# The paper

Ahmed Bou-Rabee and Ewain Gwynne, *Random walk on sphere packings and Delaunay triangulations in
arbitrary dimension*, [arXiv:2405.11673](https://arxiv.org/abs/2405.11673).

| File | Content |
|---|---|
| `rw-spheres.tex` | the source of arXiv version 2, unchanged |
| `rw-spheres.pdf` | its compiled PDF |
| `rw-spheres-corrected.tex` | the same source with the corrections, each marked by a `% CORRECTION n` or `% CLOSE n` comment and listed in its section *Corrections to the published version* |
| `rw-spheres-corrected.pdf` | its compiled PDF |
| `rw-spheres.bbl`, `rw-spheres-corrected.bbl` | the bibliography, as distributed with the arXiv source (identical files) |
| `Figures/` | the figures |

Both sources are pinned by their SHA-256 in [`../ledger/manifest.yaml`](../ledger/manifest.yaml),
and `python3 tools/check_manifest.py` checks them.  The statement map in
[`../CORRESPONDENCE.md`](../CORRESPONDENCE.md) refers to `rw-spheres.tex` by line number; the
registered statements are those of `rw-spheres-corrected.tex`.

To build either PDF, run `pdflatex` twice in this directory, for example
`pdflatex rw-spheres-corrected.tex && pdflatex rw-spheres-corrected.tex`.

The paper is posted on arXiv under the Creative Commons Attribution 4.0 International license
([CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)); the corrected version is a modified
version of it, with the changes marked, distributed under the same license.
