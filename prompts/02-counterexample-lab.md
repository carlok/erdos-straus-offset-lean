# Prompt: Counterexample Laboratory

```text
We are testing the following universal statement:

[EXACT STATEMENT]

Do not try to prove it first.

Step 1 — Logical form

- Write every quantifier and domain explicitly.
- Negate the statement exactly.
- Identify assumptions that may be redundant, ambiguous, or silently used.

Step 2 — Normalisation

- Remove equivalent cases using symmetry.
- Reduce scaling, translation, permutation, sign, or isomorphism freedom.
- Identify the smallest legal parameter values.

Step 3 — Brittle cases

Test:

- zero, one, and minimal cases;
- singular and reducible objects;
- equality and boundary cases;
- repeated or symmetric parameters;
- composite versus prime parameters;
- local conditions mistaken for global ones;
- natural-number division mistaken for rational division;
- positivity, coprimality, cancellation, or non-vanishing assumptions.

Step 4 — Exact search

Construct the smallest useful search space. Use exact integers, rationals, finite
fields, symbolic polynomials, or canonical finite objects. If code is used,
make it return a human-readable certificate rather than only "found".

Step 5 — Certificate

For every candidate counterexample:

- print the complete object;
- verify every hypothesis independently;
- display the exact failed conclusion;
- search for a smaller or simpler example;
- explain how another person can verify it without the search program.

Step 6 — Red team

Try to destroy the counterexample by checking conventions, omitted hypotheses,
degeneracy exclusions, and equivalence with known examples.

Return one of:

A. a minimal or near-minimal exact counterexample;
B. a corrected weaker statement;
C. a proof that the chosen search region contains no counterexample;
D. a precise explanation of why this target has poor research ROI.
```

