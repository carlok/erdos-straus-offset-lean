# Mathlib submission-draft report

## Status

This directory is a local, LLM-assisted candidate, not an official submission.
No pull request, issue, push, Zulip message, or maintainer contact was made.

The proposed file is `ErdosStraus.lean`, currently 742 lines. It contains 17
public definitions/results and seven private implementation lemmas. Its public
scope is listed exactly in `SELECTION.md`.

## Verified locally

Run from the repository's Lake root:

```bash
cd lean
lake env lean ../mathlib_draft/ErdosStraus.lean
```

This succeeds against the repository's pinned Lean/Mathlib dependency.

The file was also copied to its proposed path in a disposable clone of the
pinned Mathlib checkout. There:

- direct module compilation succeeded;
- `lake exe mk_all` registered it in `Mathlib.lean`;
- `#lint` reported no errors with the standard declaration linters;
- `lake exe lint-style Mathlib.NumberTheory.ErdosStraus` succeeded;
- `#redundant_imports` reported no redundant candidate import.

The following literal audits pass:

- no `sorry`, `admit`, `axiom`, or `unsafe`;
- no line longer than 100 characters;
- no `example`, explicit seed family, or paper-specific progression theorem;
- no malformed source header.

The research source `lean/ESTheorem.lean` was not changed by this extraction.

## Not yet verified

These checks used the repository's pinned Mathlib revision, not current
Mathlib `master`. Consequently the following remain mandatory:

- repeat registration and lint checks against current `master`;
- compilation of the affected import closure;
- upstream continuous integration;
- reviewer agreement on placement, naming, API size, and mathematical scope.

No claim of submission readiness should be made until these checks and human
review are complete.

## AI-assistance disclosure

The research formalization and this extraction received substantial LLM
assistance. Any future pull request must describe which tools were used and how.
Carlo must understand the code, make the submission decision, and write all
GitHub and Zulip communication in his own words, following Mathlib's policy at
the time of submission.
