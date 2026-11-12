module

public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Definitions used by the proof

These are the three definitions of `Challenge.lean`, with the same imports and the same text, so
that the proof is about exactly the notions the statement uses (Comparator checks that the
declarations agree). See `Challenge.lean` for the mathematical account.
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

end GwExact
