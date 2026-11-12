# Notes: what is proved and how it was checked (12 November 2026)

## What is proved

Everything below is proved in Lean 4 (v4.35.0, Mathlib v4.35.0) with no `sorry`, no `native_decide`
and only the axioms `propext`, `Classical.choice` and `Quot.sound`. The statements of record are in
`Challenge.lean`; `comparator.json` names the five compared theorems.

- `GwExact.gwProperty_53`: for every `r ≤ 5`, `GWProperty r 4 53`.
- `GwExact.exists_good_3`, `exists_good_4`, `exists_good_5`: good exact 3-, 4- and 5-colourings of
  `[1, 52]`.
- `GwExact.GW_eq_53`: `GW r 4 = 53` for `3 ≤ r ≤ 5`.

The upper bound rests on `GwExact.cert_ok : checkGw 53 5 4 cert = true`, proved by `decide +kernel`:
Lean's kernel runs the bitmask RUP checker over CaDiCaL's trimmed LRAT refutation (1,211 derived
clauses, 28,114 hints: 19,222 to original clauses, named by descriptors, and 8,892 to derived
clauses). `scripts/make_cert.py` rebuilt the CNF in `gw_cnf.py`'s order and found its SHA-256 equal to
the refuted CNF's (`ff0402355858a7074c8893681205c9fa1a20aea2f254cfb695e2211fdbc12072`), and checked
every descriptor against its clause; the LRAT file's SHA-256 is
`e0191268456191ba2f3cf7fe7e6b52c04923e234134fa87eb8a7e68b67760db1`. Neither check is trusted:
`run_sound` and `descCls_holds` hold for every input.

## Line counts

| File | Lines |
|---|---|
| `Challenge.lean` | 94 (4,883 bytes) |
| `Solution.lean` | 37 |
| `GwExact.lean` | 9 |
| `GwExact/Cert.lean` | 1,232 (337,799 bytes; generated) |
| `GwExact/Check.lean` | 389 |
| `GwExact/Clauses.lean` | 274 |
| `GwExact/Defs.lean` | 39 |
| `GwExact/Lower.lean` | 83 |
| `GwExact/Rank.lean` | 189 |
| `GwExact/Upper.lean` | 25 |
| `scripts/CheckAxioms.lean` | 17 |

Every `.lean` file starts with `module`; `Challenge.lean` imports only Mathlib
(`Mathlib.Order.Lattice.Nat`).

## Checks run (Mac, Apple silicon, Lean v4.35.0, machine load about 60)

All on a fresh clone of commit `811c82610b552cd967bd8b8ad078b2edd16df8ac` (the commit before this
file was added; no Lean file changed since), with the Lake packages of the pinned Mathlib checkout and
the project's own modules built from scratch.

1. `lake build`: every module built; `GwExact.Upper` (the kernel check) 12 s, peak memory of a
   separate run of the check 2.3 GB; `Challenge` has five warnings (declaration uses `sorry`, as
   intended).
2. `lake env lean scripts/CheckAxioms.lean`: `gwProperty_53` and `GW_eq_53` depend on
   `[propext, Classical.choice, Quot.sound]`; `exists_good_3/4/5` on `[propext, Quot.sound]`.
3. `lake comparator` needs bubblewrap (Linux namespaces) and does not run on macOS; the
   `--inadvisably-no-sandbox` mode was not used. Palomar's preflight workflow
   (`.github/workflows/palomar-preflight.yml`) runs it on Linux after a push. In its place, steps 4
   and 6 were run by hand.
4. Statement comparison: every constant reachable from the types of the five compared theorems
   (following definition values, not proofs) was printed with `pp.all` and hashes in the Challenge and
   in the Solution environment. The two outputs (5 roots, 120 constants) are identical except for the
   module that holds the three own definitions (`Challenge` versus `GwExact.Defs`).
5. Red controls (each must fail, and does): the certificate checked against `[1, 52]` and against
   four colours (`decide` reports the proposition false), the certificate without its last step and
   with one bit of its last step flipped (kernel rejects); the true certificate in the same file passes.
6. Kernel replays: `leanexport` wrote both modules with the compared theorems as targets; the
   Solution export (20.8 MB) was replayed through every kernel bundled with the toolchain:

   ```
   leanchecker            rc 0   16 s
   nanoda                 rc 0   18 s
   con-ron                rc 0   14 s   accepted 4354 declarations (--verified)
   leanchecker-paranoid   rc 0   23 s
   lean4lean              rc 0   19 s   checked 4351 declarations
   con-leche              rc 0   38 s   accepted 4354 declarations (--verified)
   ```

   NanoDa with unpermitted axioms as a hard error: Solution export exit 0; Challenge export exit 1
   (`export file declares unpermitted axiom "sorryAx"`), as it should. `Lean.ofReduceBool` does not
   occur in the Solution export. SHA-256 of the exports: `solution.ndjson`
   `c92686005349abf14977d4007f6115989679101ff033ba04ea2436a35774bc7c`, `challenge.ndjson`
   `b8f5f4924c75e9e310b30e918aa706d217b5db781f660c4abb5002c257a69bec`.

## What remains

- Palomar's mechanical preflight (the workflow above, on GitHub's Linux runners) has not run: it needs
  the repository to be public on GitHub. Until then the comparator itself has not run on this code
  (steps 4 to 6 replace it locally).
- No review outside Quantavane's agents.
- Not formalised: `GW(r; 3, 4)` for `r ≥ 6`; `GW(2; 3, 4) = w(4; 2) = 35`.
- Not attempted here, for scale: `GW(4; 4, 3) = 57` (its LRAT proof has 222,029 derived clauses and
  5.3 million hints, about 190 times this one) and the `l = 5` values (1.2 and 0.75 million derived
  clauses).
