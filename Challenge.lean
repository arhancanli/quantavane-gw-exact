module

public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Exact Gallai–van der Waerden numbers `GW(r; 3, 4) = 53` for `r = 3, 4, 5`: the statement

This file is the statement of record. It imports only Mathlib, defines the three notions the
statements use, and states the results with `sorry`. `Solution.lean` proves every statement;
`comparator.json` names the compared theorems. The three definitions below must agree exactly with
the ones the proof uses (Comparator checks this), so they are spelled out here in full.

## Gallai–van der Waerden numbers

Write `[1, n] = {1, …, n}`. An *exact `r`-colouring* of `[1, n]` is a colouring of `[1, n]` with
`r` colours in which every colour occurs. An arithmetic progression (AP) always has common
difference `d ≥ 1`. A 3-term AP `x, x + d, x + 2d` is *rainbow* when its three terms have three
distinct colours, and an `l`-term AP `x, x + d, …, x + (l - 1)d` is *monochromatic* when all its
terms have the same colour. The Gallai–van der Waerden number `GW(r; 3, l)` of Mao, Ozeki, Robertson
and Wang (J. Combin. Theory Ser. A 193 (2023) 105672, Definition 1.15, case `k = 3`) is the least
`m` such that, for every `n ≥ m`, every exact `r`-colouring of `[1, n]` contains a rainbow 3-term
AP or a monochromatic `l`-term AP.

* `IsGoodExactColouring r l n c`: `c` is an exact `r`-colouring of `[1, n]` with no rainbow 3-term
  AP and no monochromatic `l`-term AP in `[1, n]`.
* `GWProperty r l m`: no `[1, n]` with `n ≥ m` has such a colouring. `GW(r; 3, l)` is the least `m`
  with this property.
* `GW r l`: that least `m`, as `sInf`.

These are the definitions of the registered formalization PALOMAR-2026-11-12-000003 (namespace
`GwResidue` there), which proves the lower bounds `GW(4; 3, 4) > 52` and `GW(5; 3, 4) > 52` from a
quadratic-residue construction.

## The result

* `gwProperty_53`: for every `r ≤ 5`, every `r`-colouring of `[1, n]` with `n ≥ 53` has a rainbow
  3-term AP or a monochromatic 4-term AP. (Exactness is not needed for this direction.)
* `exists_good_3`, `exists_good_4`, `exists_good_5`: `[1, 52]` has a good exact 3-, 4- and
  5-colouring.
* `GW_eq_53`: hence `GW(r; 3, 4) = 53` for `r = 3, 4, 5`.
-/

namespace GwExact

/-- `c` is a *good exact `r`-colouring of `[1, n]`* for rainbow 3-term and monochromatic `l`-term
arithmetic progressions: every colour `col : Fin r` occurs on `[1, n]`; no `x, x + d, x + 2d` in
`[1, n]` with `d ≥ 1` has three distinct colours; and no `x, x + d, …, x + (l - 1)d` in `[1, n]`
with `d ≥ 1` has all its terms of one colour. The colouring is a function on all of `ℕ`; its values
outside `[1, n]` play no role. -/
def IsGoodExactColouring (r l n : ℕ) (c : ℕ → Fin r) : Prop :=
  (∀ col : Fin r, ∃ x, 1 ≤ x ∧ x ≤ n ∧ c x = col) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 2 * d ≤ n →
    ¬ (c x ≠ c (x + d) ∧ c x ≠ c (x + 2 * d) ∧ c (x + d) ≠ c (x + 2 * d))) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ n → ¬ ∀ j < l, c (x + j * d) = c x)

/-- `m` has the defining property of the Gallai–van der Waerden number `GW(r; 3, l)`
(Mao–Ozeki–Robertson–Wang, JCTA 2023, Def. 1.15): for every `n ≥ m`, every exact `r`-colouring of
`[1, n]` contains a rainbow 3-term AP or a monochromatic `l`-term AP, that is, no `[1, n]` with
`n ≥ m` has a good exact `r`-colouring. -/
def GWProperty (r l m : ℕ) : Prop :=
  ∀ n ≥ m, ∀ c : ℕ → Fin r, ¬ IsGoodExactColouring r l n c

/-- `GW(r; 3, l)`: the least `m` with `GWProperty r l m` (Lean's `sInf`; the infimum of the empty
set of natural numbers is `0`). -/
noncomputable def GW (r l : ℕ) : ℕ := sInf {m | GWProperty r l m}

/-- **Upper bound.** For every number `r ≤ 5` of colours and every `n ≥ 53`, no `r`-colouring of
`[1, n]` (exact or not) avoids both a rainbow 3-term AP and a monochromatic 4-term AP. In
particular `53` has the defining property of `GW(r; 3, 4)` for every `r ≤ 5`. -/
theorem gwProperty_53 (r : ℕ) (hr : r ≤ 5) : GWProperty r 4 53 := by
  sorry

/-- **Lower bound, `r = 3`.** `[1, 52]` has an exact 3-colouring with no rainbow 3-term AP and no
monochromatic 4-term AP. -/
theorem exists_good_3 : ∃ c : ℕ → Fin 3, IsGoodExactColouring 3 4 52 c := by
  sorry

/-- **Lower bound, `r = 4`.** `[1, 52]` has an exact 4-colouring with no rainbow 3-term AP and no
monochromatic 4-term AP. -/
theorem exists_good_4 : ∃ c : ℕ → Fin 4, IsGoodExactColouring 4 4 52 c := by
  sorry

/-- **Lower bound, `r = 5`.** `[1, 52]` has an exact 5-colouring with no rainbow 3-term AP and no
monochromatic 4-term AP. -/
theorem exists_good_5 : ∃ c : ℕ → Fin 5, IsGoodExactColouring 5 4 52 c := by
  sorry

/-- **The values.** `GW(r; 3, 4) = 53` for `r = 3, 4, 5`. -/
theorem GW_eq_53 (r : ℕ) (h3 : 3 ≤ r) (h5 : r ≤ 5) : GW r 4 = 53 := by
  sorry

end GwExact
