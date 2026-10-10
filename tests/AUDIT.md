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
