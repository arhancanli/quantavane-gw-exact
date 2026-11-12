# Exact Gallai–van der Waerden numbers: GW(r; 3, 4) = 53 for r = 3, 4, 5

A Lean 4 proof, with Mathlib, that the Gallai–van der Waerden numbers `GW(r; 3, 4)` of Mao, Ozeki,
Robertson and Wang equal 53 for three, four and five colours. It is laid out for registration on
[Palomar](https://palomar-registry.org): `Challenge.lean` states the results, `Solution.lean` proves
them, and `comparator.json` names the compared theorems.

## The result

Write `[1, n] = {1, …, n}`. An exact `r`-colouring of `[1, n]` uses all `r` colours. A 3-term
arithmetic progression (AP) is rainbow when its terms have three distinct colours; a 4-term AP is
monochromatic when its terms all have one colour; common differences are at least 1. Following
Mao, Ozeki, Robertson and Wang (MORW; J. Combin. Theory Ser. A 193 (2023) 105672, Definition 1.15),
`GW(r; 3, l)` is the least `m` such that for every `n ≥ m`, every exact `r`-colouring of `[1, n]`
contains a rainbow 3-term AP or a monochromatic `l`-term AP.

**Theorem.** `GW(3; 3, 4) = GW(4; 3, 4) = GW(5; 3, 4) = 53`. More precisely:

1. (upper bound) for every `r ≤ 5` and every `n ≥ 53`, every `r`-colouring of `[1, n]`, exact or
   not, has a rainbow 3-term AP or a monochromatic 4-term AP;
2. (lower bound) `[1, 52]` has an exact 3-colouring, an exact 4-colouring and an exact 5-colouring
   with neither.

## What is compared (`comparator.json`)

All five theorems are stated in `Challenge.lean` (with `sorry`) and proved in `Solution.lean`.

| Lean name | What it says |
|---|---|
| `GwExact.gwProperty_53` | For every `r ≤ 5`, `53` has the defining property of `GW(r; 3, 4)`: no `[1, n]` with `n ≥ 53` has an exact `r`-colouring without a rainbow 3-term AP and without a monochromatic 4-term AP. |
| `GwExact.exists_good_3` | `[1, 52]` has an exact 3-colouring with no rainbow 3-term AP and no monochromatic 4-term AP. |
| `GwExact.exists_good_4` | The same with 4 colours. |
| `GwExact.exists_good_5` | The same with 5 colours. |
| `GwExact.GW_eq_53` | `GW r 4 = 53` for `3 ≤ r ≤ 5`. |

`definition_names` is empty on purpose. The three definitions the statements use are spelled out in
full in `Challenge.lean`; Comparator follows them from the theorem statements and requires them to be
identical in the Solution, which takes them from `GwExact/Defs.lean`.

## Definitions, and how they match the paper

- `IsGoodExactColouring r l n c`: every colour `col : Fin r` occurs on `[1, n]`; no `x, x + d, x + 2d`
  in `[1, n]` with `d ≥ 1` has three distinct colours; no `x, x + d, …, x + (l - 1)d` in `[1, n]` with
  `d ≥ 1` is monochromatic. The colouring `c : ℕ → Fin r` is defined on all of `ℕ`; only its values on
  `[1, n]` matter.
- `GWProperty r l m`: for every `n ≥ m` and every `c`, `¬ IsGoodExactColouring r l n c`. This is the
  defining property in MORW Definition 1.15 (for every `n ≥ m`, not only `n = m`, since exactness does
  not pass to sub-intervals).
- `GW r l := sInf {m | GWProperty r l m}`. In Lean the infimum of the empty set of natural numbers is
  `0`; here the set is not empty (it contains 53), so `GW r 4` is the least threshold.

These are the definitions of the registered formalization
[PALOMAR-2026-11-12-000003](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-12-000003)
(Gallai–van der Waerden numbers from quadratic-residue colourings), which proves
`GW(4; 3, 4) > 52` and `GW(5; 3, 4) > 52` by an explicit construction. The present formalization adds
the matching upper bound, so the values are exact, and the case `r = 3`.

## How the proof goes

**Lower bounds** (`GwExact/Lower.lean`). Three explicit colourings of `[1, 52]` (point 1 first),
found by a SAT search:

- `r = 3`: `0221211122111212202212111221112122022121112211121222`
- `r = 4`: `0332322233222323313323222332223233133232223322232333`
- `r = 5`: `0112122211222121131121222112221211311212221122212114`

Each is stored as a natural number in base 8 and checked by `decide +kernel`: Lean's kernel evaluates
a Boolean test (`goodB`, proved sound by `isGood_of_goodB`) that loops over all `x, d` in `[1, 52]`.

**Upper bound** (`GwExact/Check.lean`, `Clauses.lean`, `Rank.lean`, `Cert.lean`, `Upper.lean`). The
statement "every colouring of `[1, 53]` with at most 5 colours has a rainbow 3-term AP or a
monochromatic 4-term AP" is reduced to the unsatisfiability of a propositional formula (CNF) and the
unsatisfiability is checked in Lean's kernel from a solver certificate.

- *The CNF.* Atom `i·5 + c` says that position `i` (the point `i + 1`) has colour `c < 5`. The
  clauses say: each position has a colour and not two; no 4-term AP inside `[1, 53]` is monochromatic;
  no 3-term AP is rainbow; colours appear in order of first occurrence (point 1 has colour 0, and
  colour `c ≥ 1` needs colour `c - 1` at an earlier point). There are 265 atoms and 43,562 clauses.
- *The bridge* (`Rank.lean`, `goodPos_of_colouring`). Renaming the colours of any colouring with
  `r ≤ 5` colours in order of first appearance (`rank`) gives a colouring of the positions that
  satisfies every clause. Exactness is not used for this direction.
- *The certificate* (`Cert.lean`). CaDiCaL 3.0.1 refuted the CNF and wrote an LRAT proof; after
  trimming it has 1,211 derived clauses and 28,114 hints (references to earlier clauses), the last
  derived clause being empty. `scripts/make_cert.py` writes it as one natural number per derived
  clause. Original clauses are named by short descriptors (kind and parameters) rather than by
  number.
- *The checker* (`Check.lean`, `Clauses.lean`). Clauses are pairs of bitmasks, so reverse unit
  propagation is a few operations on natural numbers that the kernel performs with GMP. `descCls`
  recomputes an original clause from its descriptor; derived clauses are kept in a binary trie.
  `run_sound` proves, for every input, that if all clauses the checker uses are true under an
  assignment then no run succeeds; `descCls_holds` proves that every descriptor clause is true for
  the renamed colouring. So the certificate is untrusted data.
- *The kernel check* (`Upper.lean`). `cert_ok : checkGw 53 5 4 cert = true` is proved by
  `decide +kernel`: the kernel evaluates the checker on the certificate. With the bridge this gives
  `GWProperty r 4 53` for every `r ≤ 5`.

**The values** (`Solution.lean`). A good exact `r`-colouring of `[1, 52]` puts every threshold above
52, and 53 is a threshold, so `GW r 4 = 53` (`GW_eq_of`).

No `sorry` outside `Challenge.lean`, no `native_decide`, no extra axioms:
`lake env lean scripts/CheckAxioms.lean` prints `[propext, Classical.choice, Quot.sound]` (or a
subset) for each compared theorem.

## Why it is of interest

Gallai–van der Waerden numbers were introduced by Mao, Ozeki, Robertson and Wang (2023) as the
arithmetic analogue of Gallai–Ramsey numbers. Exact values were known only for `l = 3` (`GW(r; 3, 3)`,
determined for every `r` by Y. Si, arXiv:2610.30711). These are, as far as we know, the first exact
values with `l = 4`, and they show that the quadratic-residue lower bound of PALOMAR-2026-11-12-000003
(`GW(r; 3, 4) > 52` for `r = 4, 5`) is sharp. For `r = 2` there is no rainbow 3-term AP and the
number is the van der Waerden number `w(4; 2) = 35`; for `r ≥ 6` the values are not determined here.
The natural readers are researchers in Ramsey theory on the integers and arithmetic combinatorics:
van der Waerden numbers, rainbow (anti-van der Waerden) problems and Gallai–Ramsey colourings.

## Provenance, literature and novelty

The values were found by Quantavane's computer search on 11 November 2026 (the CNF, the CaDiCaL
proof, an independent strict LRAT checker and the witness colourings) and are first presented here;
an internal note of Quantavane has the same statements. A literature search on 11 and 12 November
2026 (MORW; Si's arXiv paper; MathWorld's Gallai–van der Waerden page; arXiv, Zenodo, GitHub, OEIS,
Crossref and the Palomar registry) found no published value of `GW(r; 3, 4)`. The search was limited
to these sources, so novelty is our reading of it, not an established fact.

## Authorship and the role of AI

Author and maintainer: Arhan Canli (Quantavane), who takes responsibility for the result.

The computer search, the encoding, the certificate checker, its soundness proof and every line of
Lean here were produced by AI agents (Claude, by Anthropic) working for Quantavane under Arhan Canli's
direction. No mathematician outside Quantavane has reviewed the proof.

## Checking it

Lean `v4.35.0` (`lean-toolchain`) and Mathlib `v4.35.0`
(`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in `lake-manifest.json`).

```sh
lake exe cache get        # prebuilt Mathlib
lake build                # GwExact, Challenge, Solution (the kernel check takes about 15 s)
lake env lean scripts/CheckAxioms.lean
lake comparator           # Linux with bubblewrap: compares Challenge and Solution and replays the proofs
python3 scripts/make_cert.py PROOF.lrat GwExact/Cert.lean   # regenerates Cert.lean from the LRAT proof
```

`.github/workflows/palomar-preflight.yml` runs Palomar's own mechanical check
(`PalomarRegistry/PalomarSubmission`, pinned commit) on every push to `main`.

## Files

- `Challenge.lean`: the statement of record (Mathlib imports only).
- `Solution.lean`: the five compared theorems with proofs.
- `GwExact/Defs.lean`: the three definitions, identical to those in `Challenge.lean`.
- `GwExact/Check.lean`: the bitmask RUP checker and its soundness (Lean core only).
- `GwExact/Clauses.lean`: the clauses from descriptors and their truth for a colouring.
- `GwExact/Rank.lean`: the renaming of colours and the bridge to `GWProperty`.
- `GwExact/Cert.lean`: the certificate (generated by `scripts/make_cert.py`).
- `GwExact/Upper.lean`, `GwExact/Lower.lean`: the two bounds.
- `comparator.json`, `formalization.yaml`, `scripts/CheckAxioms.lean`, `scripts/make_cert.py`.

## Licence

Apache-2.0 (`LICENSE`).
