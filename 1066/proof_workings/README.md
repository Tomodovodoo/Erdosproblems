# Proof workings

This folder contains one Lamport-style, Lean-ready Markdown proof plan for each
source document in `../Proof_Files/`.

- `pollack_1985_lean_ready.md` translates `Po85.pdf`.
- `csizmadia_1998_lean_ready.md` translates `Cs98.pdf`.
- `swanepoel_2002_lean_ready.md` translates `Sw02.pdf`.
- `pach_toth_1996_lean_ready.md` translates `PaTo96.ps`.
- `pach_toth_postscript_audit.md` records source-level Figure 2 findings from
  `PaTo96.ps`, including the same/opposite orientation and non-rigid
  deformation requirements.
- `current_frontier.md` records the current Lean/document frontier as of this
  documentation pass.

The files are not verbatim paper transcriptions and are not claimed to be
completed Lean developments. They are structured proof contracts: numbered
theorems, assumptions, claims, subclaims, proof obligations, dependencies, and
Lean-shaped statements arranged so the work can be transcribed into Lean
incrementally.

Bound status convention: the basic `n / 3` construction and `n / 4` lower
bound are Lean-proved in `UnitDistanceBounds.lean` and exposed through
`KnownBounds.lean`. The Swanepoel `8 / 31`, Pach--Toth `5 / 16`, and
Csizmadia `9 / 35` bounds are not public verified Lean theorems. The bridge
modules `Swanepoel.Bridge` and `PachToth.Bridge` name the first two target
statements only as propositions, so root imports can track the intended
interfaces without presenting either in-progress bound as verified.

The current Lean frontier is documentation-first here: the lean-ready documents
are roadmaps, while the checked Lean modules formalize conditional substeps with
the remaining geometric or paper-specific obligations left as explicit theorem
hypotheses or structure fields. See `current_frontier.md` for the exact mapping
from document steps to Lean files and for the next modules to transcribe.

CI and local audits should continue to distinguish public verified theorem
wrappers from proposition-valued targets and conditional bridges. The intended
Swanepoel `8 / 31` and Pach--Toth `5 / 16` statements remain absent from the
public theorem facade until their proof terms are fully formalized without
`axiom`, `sorry`, or `admit`.

Style convention:

- Number every major claim or proof obligation.
- State dependencies before using them.
- Use division-free integer inequalities when possible.
- Mark geometric, figure-based, or omitted-paper steps explicitly instead of
  hiding them in prose.
