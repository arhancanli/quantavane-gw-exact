module

public import GwExact.Defs

@[expose] public section

/-!
# Lower bounds: good exact 3-, 4- and 5-colourings of `[1, 52]`

`goodB r l n c` is a Boolean form of `IsGoodExactColouring r l n c` (loops over `x, d ≤ n`), and
`isGood_of_goodB` proves that it is sound for `l ≥ 2`. A colouring is stored as a natural number in
base 8: point `x` gets the digit `x - 1` (`digitCol`), which the kernel reads with its built-in
`Nat.shiftRight` and `Nat.mod`. The three colourings are the witnesses found by Quantavane's SAT
search (`witnesses_52.txt`, 11 Nov 2026), point 1 first:

* `r = 3`: `0221211122111212202212111221112122022121112211121222`
* `r = 4`: `0332322233222323313323222332223233133232223322232333`
* `r = 5`: `0112122211222121131121222112221211311212221122212114`

Each is checked by `decide +kernel` (kernel evaluation of `goodB`; no `native_decide`): every colour
occurs on `[1, 52]`, no 3-term progression is rainbow and no 4-term progression is monochromatic.
-/

namespace GwExact

/-- Boolean form of `IsGoodExactColouring r l n c`. -/
def goodB (r l n : ℕ) (c : ℕ → Fin r) : Bool :=
  ((List.range r).all fun k => (List.range (n + 1)).any fun x =>
    decide (1 ≤ x) && decide (x ≤ n) && decide ((c x : ℕ) = k)) &&
  ((List.range (n + 1)).all fun x => (List.range (n + 1)).all fun d =>
    !(decide (1 ≤ x) && decide (1 ≤ d) && decide (x + 2 * d ≤ n)) ||
    !(decide ((c x : ℕ) ≠ c (x + d)) && decide ((c x : ℕ) ≠ c (x + 2 * d)) &&
      decide ((c (x + d) : ℕ) ≠ c (x + 2 * d)))) &&
  ((List.range (n + 1)).all fun x => (List.range (n + 1)).all fun d =>
    !(decide (1 ≤ x) && decide (1 ≤ d) && decide (x + (l - 1) * d ≤ n)) ||
    (List.range l).any fun j => decide ((c (x + j * d) : ℕ) ≠ c x))

theorem isGood_of_goodB {r l n : ℕ} {c : ℕ → Fin r} (hl : 2 ≤ l) (h : goodB r l n c = true) :
    IsGoodExactColouring r l n c := by
  simp only [goodB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨hall, hrb⟩, hmono⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro col
    obtain ⟨x, -, ⟨hx1, hx2⟩, hx3⟩ := hall col.val col.isLt
    exact ⟨x, hx1, hx2, Fin.ext hx3⟩
  · intro x d hx hd hxd ⟨h1, h2, h3⟩
    rcases hrb x (by omega) d (by omega) with (⟨h | h⟩ | h) | ((h | h) | h)
    · omega
    · omega
    · omega
    · exact h (Fin.val_ne_of_ne h1)
    · exact h (Fin.val_ne_of_ne h2)
    · exact h (Fin.val_ne_of_ne h3)
  · intro x d hx hd hxd hall'
    have hdl : d ≤ (l - 1) * d := Nat.le_mul_of_pos_left d (by omega)
    rcases hmono x (by omega) d (by omega) with (⟨h | h⟩ | h) | ⟨j, hj, hne⟩
    · omega
    · omega
    · omega
    · exact hne (congrArg Fin.val (hall' j hj))

/-- Point `x` gets the base-8 digit `x - 1` of `B` (reduced mod `r`). -/
def digitCol (r : ℕ) (hr : 0 < r) (B x : ℕ) : Fin r :=
  ⟨(B >>> (3 * (x - 1))) % 8 % r, Nat.mod_lt _ hr⟩

/-- The 3-colouring `0221211122111212202212111221112122022121112211121222` of `[1, 52]`. -/
def col3 : ℕ → Fin 3 := digitCol 3 (by decide) 0x49144948928a41228929125148245125224a290

/-- The 4-colouring `0332322233222323313323222332223233133232223322232333` of `[1, 52]`. -/
def col4 : ℕ → Fin 4 := digitCol 4 (by decide) 0x6da6926d24d365b4d24da49a6cb69a49b4934d8

/-- The 5-colouring `0112122211222121131121222112221211311212221122212114` of `[1, 52]`. -/
def col5 : ℕ → Fin 5 := digitCol 5 (by decide) 0x84a2922524512c945244a48a25928a489491448

theorem good3 : IsGoodExactColouring 3 4 52 col3 := isGood_of_goodB (by decide) (by decide +kernel)

theorem good4 : IsGoodExactColouring 4 4 52 col4 := isGood_of_goodB (by decide) (by decide +kernel)

theorem good5 : IsGoodExactColouring 5 4 52 col5 := isGood_of_goodB (by decide) (by decide +kernel)

end GwExact
