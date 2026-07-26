# Candidate Research Games

These are starting points, not novelty claims. Their status must be checked
again when a game begins.

## 1. Erdős--Straus period compression

**Expected ROI:** high  
**Likely outcome:** small theorem or counterexample to an overstrong period
claim  
**Lean value:** high after discovery

The current project proves that an admissible seed \((p,d,n)\) transports to
\(n+4pdk\). The period \(4pd\) is sufficient, but no minimality is claimed.

### Game

For fixed \(p,d,n\), determine when a smaller \(T>0\) preserves the full offset
certificate along \(n+Tk\).

Start from exact identities for

\[
X_p(n+Tk)-X_p(n)
\quad\text{and}\quad
B_p(n+Tk)-B_p(n).
\]

Search for:

- a counterexample to the assertion that \(4pd\) is minimal;
- necessary and sufficient divisibility conditions on \(T\);
- a gcd/lcm formula for the smallest universal transport period;
- seeds for which the period collapses dramatically;
- a converse showing which progression families arise from fixed \(d\).

**Exact win condition:** a symbolic period-compression theorem, or one explicit
seed with a provably smaller minimal period.

**Kill condition:** the proposed formula merely restates direct congruence
checking and gives no structural simplification.

Reference: the local
[`fixed_d_progression`](../lean/ESTheorem.lean) theorem and its proof.

## 2. Union-closed strengthening laboratory

**Expected ROI:** medium to high  
**Likely outcome:** a small counterexample or a restricted theorem  
**Lean value:** low for discovery, medium for a clean finite certificate

Frankl's union-closed sets conjecture asks for one element occurring in at least
half the member sets. Instead of attacking it directly, generate natural
strengthenings involving two abundant elements, separating families, minimal
set size, generators, or equality cases.

### Game

1. Formulate five plausible strengthenings that are not trivially equivalent
   to the original conjecture.
2. Search for the smallest exact counterexample to each.
3. For a surviving statement, restrict to a structurally meaningful class.
4. Prove minimality of the counterexample or prove the restricted theorem.

Represent a family canonically as bitsets and quotient by permutations of the
ground set. A certificate is simply the complete family plus its element
frequencies.

**Exact win condition:** a minimal counterexample to a natural strengthening,
or a theorem for a clean restricted class.

**Kill condition:** the strengthening was already explicitly studied or the
counterexample is a disguised textbook example.

Background:

- [Bruhn and Schaudt, *The journey of the union-closed sets
  conjecture*](https://www.uni-ulm.de/fileadmin/website_uni_ulm/mawi.inst.081/Henning/UCSurvey.pdf)
- [New conjectures for union-closed
  families](https://www.combinatorics.org/ojs/index.php/eljc/article/view/v23i3p23)

## 3. Structured lonely-runner certificates

**Expected ROI:** medium  
**Likely outcome:** counterexample to a tempting strengthening or a theorem for
a structured velocity class  
**Lean value:** medium if the final proof becomes interval-heavy

The full lonely runner conjecture is active and its small-dimensional frontier
has moved recently. A cheaper game is to study exact witness times for a
structured class of integer velocities.

### Game

Choose one class:

- velocities in arithmetic progression;
- one perturbed arithmetic progression;
- superincreasing velocities;
- velocities with a fixed gcd pattern;
- a fixed small number of runners.

Propose and test stronger statements about:

- a bounded denominator for a rational witnessing time;
- the witness lying at an endpoint of a canonical interval;
- a common witness surviving a structured perturbation;
- the number of connected components of the valid-time set.

All distances on the circle should be represented exactly by rational
inequalities.

**Exact win condition:** an exact counterexample to a natural witness-time
bound, or a symbolic theorem for one structured velocity class.

**Kill condition:** success depends on a large unstructured enumeration with no
small certificate.

Background:

- [A survey of the lonely runner
  conjecture](https://arxiv.org/abs/2409.20160)
- [Finite checking and variants](https://arxiv.org/abs/2411.06903)

## 4. Sparse Jacobian counterexample compression

**Expected ROI:** low probability, very high upside  
**Likely outcome:** a negative result inside a restricted ansatz  
**Lean value:** high for a surviving exact candidate

The recently announced three-dimensional counterexample has a constant
non-zero Jacobian determinant and an explicit rational collision. The broad
counterexample question is settled in dimensions at least three, but the search
for simpler representatives is a natural exact game.

### Game

Fix a sharply bounded ansatz in three variables and search for:

- fewer monomials;
- smaller coefficients;
- lower total degree;
- a simpler rational collision;
- a normal form under affine changes of coordinates;
- a proof that no counterexample exists inside the chosen ansatz.

Normalise affine freedom before searching. A valid counterexample certificate
must contain:

1. the three explicit polynomials;
2. an exact constant determinant identity;
3. two distinct rational inputs with the same output.

**Exact win condition:** a strictly simpler counterexample under a declared
complexity measure, or a proof excluding a meaningful finite-dimensional
ansatz.

**Kill condition:** the complexity measure is coordinate-dependent and no
normalisation makes the comparison meaningful.

This area is moving extremely quickly; literature and priority checks must be
repeated immediately before any public statement.

Background:

- [Exact audit of the announced
  counterexample](https://nasqret.github.io/jacobian-counterexample/book/index.html)
- [Independent Isabelle/HOL
  verification](https://isa-afp.org/entries/Jacobian_Counterexample.html)

## Suggested order

1. Erdős--Straus period compression.
2. Union-closed strengthening laboratory.
3. Structured lonely-runner certificates.
4. Sparse Jacobian compression as the lottery ticket.

