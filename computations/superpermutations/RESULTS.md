# Superpermutations: SAT calibration log

Machine: Ryzen 7 7840HS, Python 3.14 + python-sat (CaDiCaL 1.5.3),
single-threaded.

## What was asked

SP-2 was meant to reproduce `L(5) = 153` by SAT (UNSAT at 152), producing a
scaling curve that would decide whether SP-3 — ruling out length 871 for
n = 6, which would settle `L(6) = 872` — is worth attempting.

## What happened: the encoding does not reach n = 5

| instance | result | time |
|---|---|---|
| n = 3, L = 9 / L = 8 | SAT / UNSAT | < 0.01 s each |
| n = 4, L = 33 | SAT | 17 s (sym), 173 s (no sym) |
| n = 4, L = 32 | **UNSAT** | **54 s** |
| n = 5, L = 149 | — | **abandoned after 22.6 CPU-hours** |

`L = 149` is the *easiest* rung of the n = 5 ladder (four below the boundary,
so the most over-constrained UNSAT instance of the five). It ran at 99.5% CPU
on 889 MB for 22.6 hours without returning. Against n = 4's 54 s that is a
**> 1500× jump**, and L = 152 — the instance that would actually prove
`L(5) = 153` — is strictly harder than the one that failed.

## Verdict

* **SP-2 cannot be met with this encoding on this machine.** The curve exists
  and it is a wall, not a slope.
* **SP-3 is dead by this route, definitively.** n = 6 at L = 871 has 720
  permutations over 871 positions versus 120 over 149; if the easiest n = 5
  instance is unreachable, the n = 6 question is not a compute-budget problem
  that a forge window fixes. This is a negative result worth having: it
  removes SP-3 from the ladder rather than leaving it as perpetual "queued".
* What would change it: a fundamentally better encoding. The natural
  candidates are the permutation-graph/TSP formulation used by the
  distributed Chaffin-method searches (which is how the real bounds were
  obtained) rather than a direct symbol-assignment CNF, plus proof-logging
  UNSAT certificates. That is a project, not a parameter change.

## What is validated

The encoder itself is correct and gated: `sat.py --verify` checks SAT at
`L(n)` with an independently verified word and UNSAT at `L(n) − 1` for
n = 1..3, with and without symmetry breaking, plus a negative control (a
damaged word must be rejected). `--deep` adds n = 4, which **reproduces
L(4) = 33 exactly**. Symmetry breaking (fixing the first n positions to the
identity) buys roughly 10× and provably changes no answer at n ≤ 4.

The standing Lean result for this problem is unaffected: `L 6 ≤ 872` is
proved in `OpenProblemsLab/Superpermutations.lean` from Houston's explicit
word.
