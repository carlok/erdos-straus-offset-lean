# Prompt: Conservative Lean Gate

```text
Decide whether this result should be formalised in Lean:

[STABLE THEOREM AND HUMAN PROOF]

Recommend Lean only if it materially reduces one of these risks:

- hidden side conditions;
- exact natural-number division;
- positivity or non-zero denominators;
- modular cancellation;
- coercions between naturals, integers, finite rings, and rationals;
- a long algebraic identity;
- many interacting hypotheses;
- regression-prone parametric families.

If Lean is not justified, say so and propose a cheaper exact check.

If Lean is justified:

1. Freeze the public mathematical statement.
2. Define the semantic conclusion first.
3. Prove a division-free certificate theorem.
4. Isolate polynomial algebra from arithmetic side conditions.
5. Prove exact divisibility separately.
6. Prove positivity separately.
7. Construct witnesses only after their prerequisites are available.
8. Bridge the certificate to the semantic conclusion.
9. Add the smallest direct examples and one nontrivial regression example.
10. Report any mismatch between the intended theorem and the formal statement.

Defaults:

- use ℕ for positive parameters and witnesses;
- use ℤ for genuine subtraction;
- use ℚ only for rational identities;
- use finite rings only inside modular arguments;
- no `sorry`, unproved axioms, or opaque finite-search claims.

The final report must separate:

- what Lean proves;
- what remains prose;
- what was merely tested;
- what, if anything, is claimed about novelty.
```

