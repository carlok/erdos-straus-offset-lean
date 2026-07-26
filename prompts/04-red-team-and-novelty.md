# Prompt: Adversarial Audit and Novelty Check

```text
Audit the following proposed mathematical result:

[STATEMENT, PROOF, AND EXAMPLES]

Correctness audit:

1. Type every variable and operation.
2. Verify every division is exact or explicitly rational.
3. Check positivity, non-vanishing, primality, and coprimality.
4. Locate every cancellation and justify it in the correct ring or field.
5. Test the smallest legal inputs.
6. Test boundary and degenerate cases.
7. Attempt to falsify the strongest formulation.
8. Check that examples instantiate the displayed theorem exactly.
9. Distinguish a polynomial identity from the semantic claim it represents.
10. State the weakest theorem actually proved.

Novelty audit:

1. Search the exact statement.
2. Search equivalent parametrisations and alternate terminology.
3. Search distinctive formulas without our notation.
4. Search the numerical sequences and residue classes produced.
5. Trace survey citations into older primary literature.
6. Compare with standard classifications and known normal forms.
7. Ask whether the result is an immediate corollary of a known theorem.

Classify novelty as:

- known;
- immediate corollary;
- probably folklore;
- apparently not isolated in this form;
- tentatively novel;
- unresolved.

Absence from search results is insufficient for "tentatively novel".

Return:

- fatal correctness issues;
- repairable issues;
- strongest defensible theorem;
- strongest defensible novelty wording;
- whether expert review is needed before public mention;
- whether Lean would materially increase confidence.
```

