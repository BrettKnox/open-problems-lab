# Graceful trees: computation log

Machine: Ryzen 7 7840HS, Python 3.14, single-threaded; trees from
nauty-gentreeg (parent arrays, generated to file — the WSL pipe adds ~20 ms
latency per line, so sweeps read files).

## Headline

**Every tree on at most 18 vertices is graceful**, each with an explicit
labeling re-checked by an independent verifier (injective into {0..m}, edge
labels exactly {1..m}):

| n | trees | verified graceful | time | ms/tree |
|---|---|---|---|---|
| ≤ 15 | 15,006 total | all | 80 s (n=15: 7,741) | ~10 |
| 16 | 19,320 | 19,320 | 294 s | 15 |
| 17 | 48,629 | 48,629 | 1,401 s | 29 |
| 18 | 123,867 | 123,867 | 11,280 s | 91 |

Tree counts match OEIS A000055 exactly at every n — the generator gate.

## Method

Per tree: Aldred–McKay-style hill-climbing — a labeling of a tree is a
bijection V ↔ {0..m} (since |V| = m+1), so climb on the number of duplicated
edge labels via vertex-label swaps, moves aimed at edges whose label
currently collides, 400 restarts of ≤ 600 steps; on total failure, an exact
BFS-order backtracking search (never triggered — "ungraceful" could only be
declared by that exhaustive pass). Every positive answer is certified by the
labeling itself, independently re-verified.

The solver took three designs to get honest-and-fast: plain BFS backtracking
stalled pathologically (~46 trees/s at n=10 and hung on n=15 cases), an
extreme-first candidate order made it worse, and instrumenting restart
distributions — rather than guessing — showed the climber's stuck-restarts
were the cost driver. Gates: paths and stars as known-graceful controls,
verifier negative controls (non-injective, colliding, out-of-range labelings
all rejected), parent-array parsing round-trip.

## Standing, honestly

Fang (2010, arXiv:1003.3045) verified all trees to **35** vertices — a record
untouched for 16 years; earlier Aldred–McKay reached 27 in 1998. Our 18 is a
reproduction baseline on one laptop core in interpreted Python, not a record.
The measured cost curve (×4–8 per added vertex here; ~3.5× more trees per
vertex) says n = 19 is a day, and the mid-20s need the forge window with a
compiled climber. The harness (generator gate + verified labelings + exact
fallback) is the deliverable; a C port of the ~60-line climber is the
unblock.
