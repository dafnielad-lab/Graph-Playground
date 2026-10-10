# Audit of the solver's rules

Date: 2026-10-10. Scope: every `ge` / `le` / `eq` / `sum` call in `digest()` (src/sheet.js), the property
inheritance in `prop()`, and the pair bounds in `pairBase()` / `pairInfo()`.

## Method

1. Each rule was read and checked by hand against a theorem of the course booklet or a short direct argument.
2. `tests/soundness.js` compares every bound and every insight with the true values, on all graphs with up to
   6 vertices and on samples with 7 and 8 vertices, in about forty scenarios (plain data, degrees, colouring,
   matching, complement, every operation in both directions, components, typed lists, diameter, girth, cycles).

Neither step is a formal proof. The hand check is fallible; the test cannot see errors that only appear above 8 vertices.

## Faults found by the hand check and fixed

- Edges of components that were not defined: the bound used the largest possible number of remaining
  components, which gives the smallest room for edges. Wrong when the number of components is a range. Now uses the fewest.
- Two "k vertices of degree d" objects with the same d were added together. Now one per degree.
- Hamiltonian source, removing a set S with |S| = 0 gave c ≤ 0. Now requires |S| ≥ 1.

## Assumptions the rules rely on (not checked by the tool)

- Graphs are simple and have at least one vertex. Removing the only vertex is reported as a contradiction.
- Component objects of one graph are different components.
- "Add an edge" adds an edge that was not there.
- A set marked clique / independent really is one; its size is the size typed.
- Vertices named in two "degree count" objects with different degrees are different vertices.

## Rules that are not booklet theorems (argued directly)

m ≤ β·Δ, m ≤ ν(2Δ − 1), m ≥ χ(χ − 1)/2, c ≤ n − ν, α ≥ c, the leaf bounds in trees, the Moore bound,
g ≥ 4 ⇒ n ≥ 2δ, g ≥ 5 ⇒ n ≥ δ² + 1, the planar bound with girth, g ≤ 2·diam + 1, the bounds for removing or
returning a clique / independent set, and everything about joining the components with a minimum set of edges.


## External review, 10 October 2026

An independent review (GPT) reran the harness on every graph up to eight vertices and extended it. It found two faults that
produced false bounds on valid data, and three gaps. All are fixed, and each has a regression case in `soundness.js`.

| Finding | Fix |
|---|---|
| The automatic operation "remove two adjacent vertices" was created when n could be 2, leaving no vertex; the back-relation then raised n and α of the source (K2 as a forest with two leaves gave n ≥ 3, α ≥ 2). | The operation is created only when n ≥ 3. |
| The Moore bound stopped summing at one million and used the partial sum as an upper bound on n (full binary tree of depth 20 was reported contradictory). | The bound is applied only when every layer was summed. |
| A degree sequence was checked for parity and maximum only; 2,659 of 2,727 impossible sequences in the tested range passed. | Erdős–Gallai test, both in the data warnings and in the solver. |
| Displayed formulas without their conditions: Hamiltonian c(G − S) ≤ \|S\| needs S ≠ ∅; after joining components χ′ = max(χ, 2) needs c ≥ 2; the Eulerian row δ ≥ 2, m ≥ n needs n ≥ 2. | Conditions added to the displayed text. The computations were already right. |
| The number of vertices of degree one was taken from a degree sequence or a degree count only in a forest. | Taken in every graph. |

Changes to the harness, following the same review:

- The digest path is tested: `SHEET.solve(list, true)` adds the automatic operations of every object, as the digest does (scenarios A1–A6). The earlier harness never ran this path, which is how the first fault escaped.
- Fixed cases beyond the catalogue (R1–R8): the two reported faults, a non-graphic sequence, and large paths, cycles, complete graphs and stars.
- The "simple cycle on at least k vertices" insight is now checked against the real cycle lengths.
- The process exits with a non-zero code on any violation, and says so when it stopped early.
- The solver reports when a round budget stopped the inference (`cap`); the digest shows a warning in that case. No run has hit the budget.
- Browser and page paths come from `CHROMIUM` and `PAGE`, with the repository's own `index.html` as the default.

Result after the fixes: no violations on every graph up to eight vertices, automatic operations included.
Passing these tests is evidence, not a proof of every rule at every size.
