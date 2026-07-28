# Mathlib draft checklist

## Completed locally

- [x] Standard copyright header
- [x] Current `module` / `public import` shell
- [x] Module docstring before declarations
- [x] `@[expose] public section`
- [x] Explicit imports rather than `import Mathlib`
- [x] Paper-specific families and examples removed
- [x] Implementation-only helpers made private
- [x] No `sorry`, `admit`, `axiom`, or `unsafe`
- [x] No line over 100 characters
- [x] Standalone draft compiles against the pinned project dependency
- [x] Draft compiles from its proposed path in a disposable Mathlib checkout
- [x] `lake exe mk_all` registers the module
- [x] Mathlib declaration linters pass
- [x] `lake exe lint-style Mathlib.NumberTheory.ErdosStraus` passes
- [x] `#redundant_imports` reports no redundant candidate import
- [x] Reports describe the delivered file

## Required before an upstream proposal

- [ ] Carlo understands and can explain every declaration and design decision
- [ ] Discuss scope, placement, and naming on Lean Zulip in Carlo's own words
- [ ] Copy the file into a fresh checkout of current Mathlib `master`
- [ ] Run `lake exe mk_all`
- [ ] Run the applicable Mathlib linters
- [ ] Recheck imports and linters if current `master` differs from the pinned version
- [ ] Build the affected import closure
- [ ] Obtain clean upstream CI
- [ ] Disclose the specific AI assistance in the PR description
- [ ] Apply the `LLM-generated` label if required by the current policy
