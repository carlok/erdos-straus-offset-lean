# Small Exact Mathematics Research Game

This folder contains prompts for a conversational search for small mathematical
results with unusually good research return on effort.

The ideal result is:

- understandable in one paragraph, at no more than graduate level;
- related to a genuine open problem or an active mathematical question;
- represented by a short exact certificate;
- independently checkable without trusting the model;
- either a counterexample, a small theorem, a new family, or a useful negative
  result;
- formalised in Lean only when formalisation materially improves confidence.

The game is not to ask an LLM to solve a famous conjecture directly. The game is
to find a brittle nearby assertion: a converse, strengthening, boundary case,
periodicity claim, restricted ansatz, or hidden assumption.

## The ROI test

A target has high research ROI when:

1. its statement is cheaper to understand than its significance;
2. a success has a compact exact certificate;
3. failed approaches eliminate a meaningful region of the search space;
4. the literature can be searched using distinctive formulas or parameters;
5. proof engineering is small relative to the mathematical content.

A good win may be only one page of mathematics. A failed hunt is still useful
if it produces a precise obstruction or a counterexample to a tempting lemma.

## How to play

1. Start a chat with [`00-game-master.md`](00-game-master.md).
2. Use [`01-target-scout.md`](01-target-scout.md) to select a target.
3. Choose either [`02-counterexample-lab.md`](02-counterexample-lab.md) or
   [`03-small-theorem-miner.md`](03-small-theorem-miner.md).
4. Run [`04-red-team-and-novelty.md`](04-red-team-and-novelty.md) before
   describing anything as a result.
5. Use [`05-lean-gate.md`](05-lean-gate.md) only after the mathematical
   statement has stabilised.

Several starting points are collected in [`CANDIDATES.md`](CANDIDATES.md).

## Rules of the game

- Exact arithmetic is evidence; floating-point agreement is not.
- A model-generated proof must be attacked before it is polished.
- Computation may discover a certificate but must not be hidden in prose.
- Lean establishes correctness of a statement, not novelty or importance.
- Absence from a web search is not evidence of priority.
- If a candidate dies quickly, record why and move on.
- Prefer a modest true result over an impressive ambiguous one.

