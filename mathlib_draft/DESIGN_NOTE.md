# Design note

This directory is a local, LLM-assisted candidate extraction from
`lean/ESTheorem.lean`. It is not an official Mathlib submission.

## Proposed placement

The tentative location is:

```text
Mathlib/NumberTheory/ErdosStraus.lean
```

with namespace `ErdosStraus`. Placement and API names should be discussed by
Carlo on the Lean Zulip before opening a pull request.

The draft follows current module syntax:

```lean
module

public import ...

/-! module documentation -/

@[expose] public section
```

A new file in a real Mathlib checkout must be registered by running
`lake exe mk_all`, which updates the generated root `Mathlib.lean` file.

## Scope

The proposed library unit contains:

- the positive natural-number/rational Erdős–Straus predicate;
- a division-free positive certificate;
- the constructive offset theorem;
- packaged offset admissibility;
- transport by `4 * p * d`;
- general transport identities;
- an exact characterization of valid positive transport steps;
- the theorem that `4 * p * d` is the least positive transport period.

Explicit seed families, regression examples, integer-only families, paper
exposition, and computational experiments are intentionally absent.

## Open design questions

- Whether the topic belongs directly under `NumberTheory` or under a future
  Egyptian-fractions directory.
- Whether `IsES` should receive a more descriptive permanent API name.
- Whether the constructive material and period characterization should remain
  in one file or be split after reviewer feedback.
- Whether some private algebraic or specialized transport helpers should be
  replaced by existing Mathlib lemmas.

