module

public import GwExact.Defs
public import GwExact.Clauses
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

@[expose] public section

/-!
# From a good colouring to a model of the CNF

A colouring `c : ℕ → Fin r` with `r ≤ R`, no rainbow 3-term AP and no monochromatic `l`-term AP in
`[1, n]` becomes, after renaming its colours in order of first appearance (`rank`), a colouring of
the positions `0, …, n - 1` with the properties `GoodPos n R l` (`goodPos_of_colouring`). With the
soundness of the checker (`checkGw_sound`) this gives the GW property at `n` for every `r ≤ R`
(`gwProperty_of_check`). Exactness (all `r` colours used) is not needed for this direction.

The renaming (`rank`): position `i` gets the number of distinct colours that occur before the first
position with the colour of `i`. It has the same equal/unequal pattern as the colouring
(`rank_eq_iff`), it is below `r` (`rank_lt_card`), position `0` gets `0` (`rank_zero`), and a rank
`k ≥ 1` at `i` occurs as `k - 1` at an earlier position (`rank_pred`).

Ported from Quantavane's `GwResidue/Bridge.lean` (Lean v4.33.1, 11 Nov 2026).
-/

namespace GwExact

section Rename

variable {α : Type*} [DecidableEq α] (f : ℕ → α)

/-- The first position with the same colour as position `i`. -/
noncomputable def firstPos (i : ℕ) : ℕ := Nat.find (⟨i, rfl⟩ : ∃ j, f j = f i)

theorem firstPos_spec (i : ℕ) : f (firstPos f i) = f i :=
  Nat.find_spec (⟨i, rfl⟩ : ∃ j, f j = f i)

theorem firstPos_le (i : ℕ) : firstPos f i ≤ i :=
  Nat.find_min' (⟨i, rfl⟩ : ∃ j, f j = f i) rfl

theorem ne_of_lt_firstPos {i j : ℕ} (h : j < firstPos f i) : f j ≠ f i :=
  Nat.find_min (⟨i, rfl⟩ : ∃ j, f j = f i) h

theorem firstPos_congr {i i' : ℕ} (h : f i = f i') : firstPos f i = firstPos f i' :=
  le_antisymm (Nat.find_min' _ ((firstPos_spec f i').trans h.symm))
    (Nat.find_min' _ ((firstPos_spec f i).trans h))

/-- The number of distinct colours at the positions `< m`. -/
noncomputable def numCols (m : ℕ) : ℕ := ((Finset.range m).image f).card

theorem numCols_zero : numCols f 0 = 0 := by simp [numCols]

theorem numCols_mono {m m' : ℕ} (h : m ≤ m') : numCols f m ≤ numCols f m' :=
  Finset.card_le_card (Finset.image_subset_image (Finset.range_subset_range.mpr h))

theorem numCols_succ_of_mem {m : ℕ} (h : f m ∈ (Finset.range m).image f) :
    numCols f (m + 1) = numCols f m := by
  rw [numCols, numCols, Finset.range_add_one, Finset.image_insert, Finset.insert_eq_of_mem h]

theorem numCols_succ_of_notMem {m : ℕ} (h : f m ∉ (Finset.range m).image f) :
    numCols f (m + 1) = numCols f m + 1 := by
  rw [numCols, numCols, Finset.range_add_one, Finset.image_insert, Finset.card_insert_of_notMem h]

theorem notMem_firstPos (i : ℕ) : f (firstPos f i) ∉ (Finset.range (firstPos f i)).image f := by
  intro h
  obtain ⟨j, hj, hfj⟩ := Finset.mem_image.mp h
  exact ne_of_lt_firstPos f (Finset.mem_range.mp hj) (hfj.trans (firstPos_spec f i))

/-- The rank of the colour of position `i` in order of first appearance. -/
noncomputable def rank (i : ℕ) : ℕ := numCols f (firstPos f i)

theorem rank_lt_rank {i i' : ℕ} (h : firstPos f i < firstPos f i') : rank f i < rank f i' := by
  have h1 := numCols_succ_of_notMem f (notMem_firstPos f i)
  have h2 := numCols_mono f (show firstPos f i + 1 ≤ firstPos f i' by omega)
  unfold rank
  omega

/-- The renaming keeps the equal/unequal pattern of the colouring. -/
theorem rank_eq_iff {i i' : ℕ} : rank f i = rank f i' ↔ f i = f i' := by
  constructor
  · intro h
    by_contra hne
    have hp : firstPos f i ≠ firstPos f i' := fun hp =>
      hne ((firstPos_spec f i).symm.trans ((congrArg f hp).trans (firstPos_spec f i')))
    rcases Nat.lt_or_gt_of_ne hp with hlt | hlt
    · have := rank_lt_rank f hlt
      omega
    · have := rank_lt_rank f hlt
      omega
  · intro h
    unfold rank
    rw [firstPos_congr f h]

theorem rank_zero : rank f 0 = 0 := by
  have h : firstPos f 0 = 0 := Nat.le_zero.mp (firstPos_le f 0)
  rw [rank, h, numCols_zero]

theorem exists_rank_pred : ∀ m, 1 ≤ numCols f m → ∃ j < m, rank f j + 1 = numCols f m := by
  intro m
  induction m with
  | zero =>
    intro h
    rw [numCols_zero] at h
    omega
  | succ m ih =>
    intro h
    by_cases hm : f m ∈ (Finset.range m).image f
    · rw [numCols_succ_of_mem f hm] at h ⊢
      obtain ⟨j, hj, hj'⟩ := ih h
      exact ⟨j, by omega, hj'⟩
    · refine ⟨m, by omega, ?_⟩
      have hfm : firstPos f m = m := by
        apply le_antisymm (firstPos_le f m)
        by_contra hlt
        exact hm (Finset.mem_image.mpr
          ⟨firstPos f m, Finset.mem_range.mpr (by omega), firstPos_spec f m⟩)
      rw [numCols_succ_of_notMem f hm, rank, hfm]

/-- A rank `k ≥ 1` at position `i` occurs as rank `k - 1` at an earlier position. -/
theorem rank_pred {i : ℕ} (h : 1 ≤ rank f i) : ∃ j < i, rank f j + 1 = rank f i := by
  obtain ⟨j, hj, hj'⟩ := exists_rank_pred f (firstPos f i) h
  exact ⟨j, lt_of_lt_of_le hj (firstPos_le f i), hj'⟩

end Rename

/-- With `r` colours, every rank is below `r`. -/
theorem rank_lt_card {r : ℕ} (f : ℕ → Fin r) (i : ℕ) : rank f i < r := by
  have hsub : (Finset.range (firstPos f i)).image f ⊆ Finset.univ.erase (f i) := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_erase.mpr ⟨ne_of_lt_firstPos f (Finset.mem_range.mp hj), Finset.mem_univ _⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
  have h2 : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) (f i).isLt
  unfold rank numCols
  omega

/-- **Bridge.** A colouring `c : ℕ → Fin r` with `r ≤ R`, no rainbow 3-term AP and no monochromatic
`l`-term AP in `[1, n]`, renamed in order of first appearance, has the properties `GoodPos n R l`
on the positions `0, …, n - 1` (position `i` is the point `i + 1`). -/
theorem goodPos_of_colouring {r R l n : ℕ} (hrR : r ≤ R) (c : ℕ → Fin r)
    (hrb : ∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 2 * d ≤ n →
      ¬ (c x ≠ c (x + d) ∧ c x ≠ c (x + 2 * d) ∧ c (x + d) ≠ c (x + 2 * d)))
    (hmono : ∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ n → ¬ ∀ j < l, c (x + j * d) = c x) :
    GoodPos n R l (rank fun i => c (i + 1)) := by
  set f : ℕ → Fin r := fun i => c (i + 1) with hfdef
  have hf : ∀ i i', rank f i = rank f i' ↔ c (i + 1) = c (i' + 1) := fun i i' => rank_eq_iff f
  refine ⟨fun i => lt_of_lt_of_le (rank_lt_card f i) hrR, rank_zero f, ?_, ?_, ?_⟩
  · intro i hi
    exact rank_pred f hi
  · intro a d hd had
    by_contra hcon
    push Not at hcon
    apply hmono (a + 1) d (by omega) hd (by omega)
    intro j hj
    have h2 := (hf (a + j * d) a).mp (hcon j hj)
    rwa [show a + j * d + 1 = a + 1 + j * d by omega] at h2
  · intro a d hd had hall
    apply hrb (a + 1) d (by omega) hd (by omega)
    obtain ⟨h1, h2, h3⟩ := hall
    refine ⟨fun h => h1 ((hf _ _).mpr ?_), fun h => h2 ((hf _ _).mpr ?_),
      fun h => h3 ((hf _ _).mpr ?_)⟩
    · rwa [show a + d + 1 = a + 1 + d by omega]
    · rwa [show a + 2 * d + 1 = a + 1 + 2 * d by omega]
    · rwa [show a + d + 1 = a + 1 + d by omega, show a + 2 * d + 1 = a + 1 + 2 * d by omega]

/-- A certificate accepted by the checker for `(n, R, l)` gives the GW property at `n` for every
number `r ≤ R` of colours. -/
theorem gwProperty_of_check {r R l n : ℕ} (hrR : r ≤ R) {steps : List Nat}
    (h : checkGw n R l steps = true) : GWProperty r l n := by
  intro m hm c hc
  obtain ⟨_, hrb, hmono⟩ := hc
  exact checkGw_sound steps h (goodPos_of_colouring (n := n) (l := l) hrR c
    (fun x d hx hd _ => hrb x d hx hd (by omega)) (fun x d hx hd _ => hmono x d hx hd (by omega)))

/-- A good exact colouring of `[1, n]` puts every GW threshold above `n`. -/
theorem lt_of_good {r l n : ℕ} {c : ℕ → Fin r} (hc : IsGoodExactColouring r l n c) {m : ℕ}
    (hm : GWProperty r l m) : n < m := by
  by_contra h
  exact hm n (not_lt.mp h) c hc

/-- A good exact `r`-colouring of `[1, n]` and the GW property at `n + 1` pin down `GW r l = n + 1`. -/
theorem GW_eq_of {r l n : ℕ} {c : ℕ → Fin r} (hgood : IsGoodExactColouring r l n c)
    (hup : GWProperty r l (n + 1)) : GW r l = n + 1 :=
  le_antisymm (Nat.sInf_le hup) (le_csInf ⟨n + 1, hup⟩ fun _ hm => lt_of_good hgood hm)

end GwExact
