# Preservation audit

Source: `lean/ESTheorem.lean`.

## Preserved mathematical interface

The draft retains the source statements and proof substance for:

- the positive Erdős–Straus representation predicate;
- the positive polynomial and offset-certificate bridges;
- modular complementary-factor cancellation;
- the constructive offset theorem;
- fixed-divisor admissibility and transport;
- the general transport identities;
- polynomial divisibility;
- exact valid-period characterization;
- period divisibility and least-positive-period results.

`OffsetAdmissible` is represented as an eight-field proposition-valued
structure. Its fields are exactly the eight hypotheses used by the constructive
offset theorem.

## Intentional removals

The following source material is not part of this candidate library API:

- integer-only Mordell and Family I statements;
- explicit seed and progression corollaries;
- regression examples;
- the tautological `es_polynomial`;
- the general-purpose integer `engine_lemma`;
- public fixed-progression convenience wrappers.

The internal integer polynomial calculation needed by the positive certificate
is retained as a private lemma.

## High-risk proof

`divisor_dvd_quarter_step` is the most intricate proof in the file. It uses
prime factorization and valuation bounds to show that the two period
divisibility conditions force `d ∣ T / 4`. A human contributor should review
this proof and its surrounding API line by line before proposing it upstream.

