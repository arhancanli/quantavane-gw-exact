module

public import GwExact

public section

/-!
# Proofs of the statements in `Challenge.lean`

Each theorem below has exactly the statement of its counterpart in `Challenge.lean` (Comparator
checks this, together with the definitions the statements use, which come from `GwExact.Defs`).

* `gwProperty_53`: `GwExact.Upper` (`cert_ok`: the kernel check of the LRAT certificate;
  `gwProperty_of_check`: the checker's soundness and the renaming of colours in `GwExact.Rank`);
* `exists_good_3`, `exists_good_4`, `exists_good_5`: the explicit colourings of `GwExact.Lower`,
  checked by `decide +kernel`;
* `GW_eq_53`: both bounds together (`GW_eq_of`).
-/

namespace GwExact

theorem gwProperty_53 (r : ℕ) (hr : r ≤ 5) : GWProperty r 4 53 :=
  gwProperty_53_of_le hr

theorem exists_good_3 : ∃ c : ℕ → Fin 3, IsGoodExactColouring 3 4 52 c := ⟨col3, good3⟩

theorem exists_good_4 : ∃ c : ℕ → Fin 4, IsGoodExactColouring 4 4 52 c := ⟨col4, good4⟩

theorem exists_good_5 : ∃ c : ℕ → Fin 5, IsGoodExactColouring 5 4 52 c := ⟨col5, good5⟩

theorem GW_eq_53 (r : ℕ) (h3 : 3 ≤ r) (h5 : r ≤ 5) : GW r 4 = 53 := by
  rcases (by omega : r = 3 ∨ r = 4 ∨ r = 5) with rfl | rfl | rfl
  · exact GW_eq_of good3 (gwProperty_53 3 (by decide))
  · exact GW_eq_of good4 (gwProperty_53 4 (by decide))
  · exact GW_eq_of good5 (gwProperty_53 5 (by decide))

end GwExact
