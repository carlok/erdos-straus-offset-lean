# Lean-verified Erdős–Straus offset construction

This repository contains a self-contained Lean 4 formalization and companion
TeX note for a classical divisor-split construction for

```text
4/n = 1/x + 1/y + 1/z.
```

The Erdős–Straus conjecture remains open. This project makes no claim of
resolving it, no priority claim for the construction or its formalization, and
no computational coverage or density claim.

## What is formalized

`lean/ESTheorem.lean` proves:

- `IsES`: positive natural denominators and the unit-fraction equality in `ℚ`;
- the bridge from the cross-multiplied polynomial identity to `IsES`;
- a positive, division-free offset certificate;
- complementary-factor cancellation in `ZMod p`;
- `constructive_offset`, which constructs the natural denominators, proves all
  divisions exact and all denominators positive, and concludes `IsES`;
- Family I and the `p = 3`, `d₁ = 2, 5` infinite progressions stated in the
  paper;
- regression instances at `k = 0` and `k = 1` for every progression.

The canonical paper is `tex/arxiv.tex`.

## Build

Lean:

```bash
cd lean
lake build
```

TeX:

```bash
cd tex
pdflatex -interaction=nonstopmode -halt-on-error arxiv.tex
pdflatex -interaction=nonstopmode -halt-on-error arxiv.tex
```

The project pins Lean and Mathlib to `v4.32.1`.
