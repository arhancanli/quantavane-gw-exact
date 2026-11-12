module

public import GwExact.Check

@[expose] public section

/-!
# The clauses of the GW CNF, recomputed from descriptors

The CNF behind `GW(r; 3, l) ≤ n` (Quantavane's `gw_cnf.py n R 3 l`) says that the positions
`0, …, n - 1` (the points `1, …, n`) get colours below `R` with no rainbow 3-term and no
monochromatic `l`-term progression, colours numbered in order of first appearance. Atom `i * R + c`
says that position `i` has colour `c`. Instead of building the CNF (43,562 clauses for
`(n, R, l) = (53, 5, 4)`), the checker recomputes each clause a hint names from a short descriptor
(`descCls`), and `descCls_holds` shows that every such clause is true for the assignment `asg R col`
of a colouring `col` with the properties `GoodPos n R l col`.

Descriptor layout (least significant bits first): kind (3 bits), then fields `f1, …, f5` of 8 bits.
* kind 0: position `f1` has a colour below `R`;
* kind 1: position `f1` does not have both colours `f2 < f3` (below `R`);
* kind 2: the positions `f1 + j f2` (`j < l`, `f2 ≥ 1`, `f1 + (l - 1) f2 < n`) do not all have
  colour `f3 < R`;
* kind 3: the positions `f1, f1 + f2, f1 + 2 f2` (`f2 ≥ 1`, `f1 + 2 f2 < n`) do not have the
  distinct colours `f3, f4, f5` (below `R`) in this order;
* kind 4: position `0` has colour `0`;
* kind 5: colour `f2` (`1 ≤ f2 < R`) at position `f1` needs colour `f2 - 1` at a position `< f1`.
-/

namespace GwExact

/-- The bit of atom `v`. -/
def bit (v : Nat) : Nat := Nat.shiftLeft 1 v

/-- The atoms "position `a + j d` has colour `c`" for `j < m`. -/
def monoMask (R c a d : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => Nat.lor (monoMask R c a d j) (bit (Nat.add (Nat.mul (Nat.add a (Nat.mul j d)) R) c))

/-- The atoms "position `j` has colour `0`" for `j < i` (shift by `c` for colour `c`). -/
def rep (R : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => Nat.lor (rep R i) (bit (Nat.mul i R))

/-- The clause of a descriptor, or `none` for an invalid descriptor. -/
def descCls (n R l code : Nat) : Option Cls :=
  let kind := Nat.land code 7
  let f1 := Nat.land (Nat.shiftRight code 3) 255
  let f2 := Nat.land (Nat.shiftRight code 11) 255
  let f3 := Nat.land (Nat.shiftRight code 19) 255
  let f4 := Nat.land (Nat.shiftRight code 27) 255
  let f5 := Nat.land (Nat.shiftRight code 35) 255
  cond (Nat.beq kind 0)
    (some ⟨Nat.shiftLeft (Nat.sub (bit R) 1) (Nat.mul f1 R), 0⟩)
  (cond (Nat.beq kind 1)
    (cond (Nat.blt f2 f3 && Nat.blt f3 R)
      (some ⟨0, Nat.lor (bit (Nat.add (Nat.mul f1 R) f2)) (bit (Nat.add (Nat.mul f1 R) f3))⟩) none)
  (cond (Nat.beq kind 2)
    (cond (Nat.ble 1 f2 && Nat.blt (Nat.add f1 (Nat.mul (Nat.sub l 1) f2)) n && Nat.blt f3 R)
      (some ⟨0, monoMask R f3 f1 f2 l⟩) none)
  (cond (Nat.beq kind 3)
    (cond (Nat.ble 1 f2 && Nat.blt (Nat.add f1 (Nat.mul 2 f2)) n && Nat.blt f3 R && Nat.blt f4 R &&
        Nat.blt f5 R && !Nat.beq f3 f4 && !Nat.beq f3 f5 && !Nat.beq f4 f5)
      (some ⟨0, Nat.lor (Nat.lor (bit (Nat.add (Nat.mul f1 R) f3))
        (bit (Nat.add (Nat.mul (Nat.add f1 f2) R) f4)))
        (bit (Nat.add (Nat.mul (Nat.add f1 (Nat.mul 2 f2)) R) f5))⟩) none)
  (cond (Nat.beq kind 4)
    (cond (Nat.blt 0 R) (some ⟨1, 0⟩) none)
  (cond (Nat.beq kind 5)
    (cond (Nat.ble 1 f2 && Nat.blt f2 R)
      (some ⟨Nat.shiftLeft (rep R f1) (Nat.sub f2 1), bit (Nat.add (Nat.mul f1 R) f2)⟩) none)
  none)))))

/-- The clause source of the GW certificate: odd hints name derived clauses (by index), even
hints name original clauses (by descriptor). -/
def gwSrc (n R l : Nat) (db : Trie) (h : Nat) : Option Cls :=
  cond (Nat.beq (Nat.land h 1) 1) (db.find (Nat.shiftRight h 1)) (descCls n R l (Nat.shiftRight h 1))

/-- The checker for the GW CNF with hints of 44 bits. -/
def checkGw (n R l : Nat) (steps : List Nat) : Bool :=
  run (gwSrc n R l) 44 17592186044415 .leaf 0 steps

/-! ## Soundness -/

/-- The properties of a colouring of the positions `0, …, n - 1` that the CNF encodes: colours
below `R`, colour `0` at position `0`, colours in order of first appearance, no monochromatic
`l`-term and no rainbow 3-term progression (with difference `≥ 1`) inside `[0, n)`. -/
structure GoodPos (n R l : Nat) (col : Nat → Nat) : Prop where
  lt : ∀ i, col i < R
  zero : col 0 = 0
  pred : ∀ i, 1 ≤ col i → ∃ j < i, col j + 1 = col i
  mono : ∀ a d, 1 ≤ d → a + (l - 1) * d < n → ∃ j < l, col (a + j * d) ≠ col a
  rb : ∀ a d, 1 ≤ d → a + 2 * d < n →
    ¬ (col a ≠ col (a + d) ∧ col a ≠ col (a + 2 * d) ∧ col (a + d) ≠ col (a + 2 * d))

/-- The assignment of a colouring: atom `v` is true iff position `v / R` has colour `v % R`. -/
def asg (R : Nat) (col : Nat → Nat) (v : Nat) : Bool := decide (col (v / R) = v % R)

theorem asg_gv {R : Nat} {col : Nat → Nat} {i c : Nat} (hc : c < R) :
    asg R col (i * R + c) = decide (col i = c) := by
  have hR : 0 < R := by omega
  have h1 : (i * R + c) / R = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right c i hR, Nat.div_eq_of_lt hc, Nat.zero_add]
  have h2 : (i * R + c) % R = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  simp only [asg, h1, h2]

theorem testBit_bit (v u : Nat) : (bit v).testBit u = decide (v = u) := by
  show (1 <<< v).testBit u = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_lor' (a b u : Nat) : (Nat.lor a b).testBit u = (a.testBit u || b.testBit u) :=
  Nat.testBit_or a b u

theorem monoMask_bit (R c a d : Nat) : ∀ m j, j < m →
    (monoMask R c a d m).testBit ((a + j * d) * R + c) = true := by
  intro m
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
    intro j hj
    show (Nat.lor (monoMask R c a d m) (bit ((a + m * d) * R + c))).testBit _ = true
    rw [testBit_lor', Bool.or_eq_true]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · exact Or.inl (ih j hj)
    · right; rw [testBit_bit]; subst hj; simp

theorem rep_bit (R : Nat) : ∀ i j, j < i → (rep R i).testBit (j * R) = true := by
  intro i
  induction i with
  | zero => intro j hj; omega
  | succ i ih =>
    intro j hj
    show (Nat.lor (rep R i) (bit (i * R))).testBit _ = true
    rw [testBit_lor', Bool.or_eq_true]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
    · exact Or.inl (ih j hj)
    · right; rw [testBit_bit]; subst hj; simp

/-- A negative literal "position `i` does not have colour `c`" that is true makes the clause true. -/
theorem holds_neg {R : Nat} {col : Nat → Nat} {cl : Cls} {i c : Nat} (hc : c < R)
    (hbit : cl.n.testBit (i * R + c) = true) (hne : col i ≠ c) : cl.Holds (asg R col) :=
  ⟨i * R + c, Or.inr ⟨hbit, by rw [asg_gv hc]; simp [hne]⟩⟩

/-- A positive literal "position `i` has colour `c`" that is true makes the clause true. -/
theorem holds_pos {R : Nat} {col : Nat → Nat} {cl : Cls} {i c : Nat} (hc : c < R)
    (hbit : cl.p.testBit (i * R + c) = true) (heq : col i = c) : cl.Holds (asg R col) :=
  ⟨i * R + c, Or.inl ⟨hbit, by rw [asg_gv hc]; simp [heq]⟩⟩

theorem not_beq_iff (a b : Nat) : (!Nat.beq a b) = true ↔ a ≠ b := by
  cases h : Nat.beq a b
  · simp only [Bool.not_false, true_iff]; intro e; subst e; simp at h
  · simp only [Bool.not_true, Bool.false_eq_true, false_iff, Classical.not_not]
    exact Nat.eq_of_beq_eq_true h

/-- Every clause computed from a descriptor is true for the assignment of a colouring with the
properties `GoodPos`. -/
theorem descCls_holds {n R l : Nat} {col : Nat → Nat} (hcol : GoodPos n R l col) (code : Nat)
    {cl : Cls} (h : descCls n R l code = some cl) : cl.Holds (asg R col) := by
  simp only [descCls, Bool.cond_eq_ite, Nat.beq_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
    not_beq_iff, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] at h
  generalize Nat.land code 7 = kind at h
  generalize Nat.land (Nat.shiftRight code 3) 255 = f1 at h
  generalize Nat.land (Nat.shiftRight code 11) 255 = f2 at h
  generalize Nat.land (Nat.shiftRight code 19) 255 = f3 at h
  generalize Nat.land (Nat.shiftRight code 27) 255 = f4 at h
  generalize Nat.land (Nat.shiftRight code 35) 255 = f5 at h
  have hR : ∀ i, col i < R := hcol.lt
  split at h
  · -- kind 0: some colour at position f1
    cases h
    have hc := hR f1
    refine holds_pos hc ?_ rfl
    show (Nat.shiftLeft (bit R - 1) (f1 * R)).testBit (f1 * R + col f1) = true
    have : bit R - 1 = 2 ^ R - 1 := by
      show (1 <<< R) - 1 = 2 ^ R - 1
      rw [Nat.one_shiftLeft]
    show ((bit R - 1) <<< (f1 * R)).testBit (f1 * R + col f1) = true
    rw [this, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    simp [hc]
  split at h
  · -- kind 1: not two colours at position f1
    split at h
    · cases h
      rename_i hv
      obtain ⟨h23, h3R⟩ := hv
      by_cases ha : col f1 = f2
      · refine holds_neg (i := f1) (c := f3) h3R ?_ (by omega)
        show (Nat.lor (bit (f1 * R + f2)) (bit (f1 * R + f3))).testBit _ = true
        rw [testBit_lor', testBit_bit, testBit_bit]; simp
      · refine holds_neg (i := f1) (c := f2) (by omega) ?_ ha
        show (Nat.lor (bit (f1 * R + f2)) (bit (f1 * R + f3))).testBit _ = true
        rw [testBit_lor', testBit_bit, testBit_bit]; simp
    · cases h
  split at h
  · -- kind 2: no monochromatic l-term progression
    split at h
    · cases h
      rename_i hv
      obtain ⟨⟨hd, hn⟩, h3R⟩ := hv
      obtain ⟨j, hj, hne⟩ := hcol.mono f1 f2 hd hn
      by_cases ha : col f1 = f3
      · refine holds_neg (i := f1 + j * f2) (c := f3) h3R (monoMask_bit R f3 f1 f2 l j hj) ?_
        rw [← ha]; exact hne
      · refine holds_neg (i := f1 + 0 * f2) (c := f3) h3R (monoMask_bit R f3 f1 f2 l 0 (by omega)) ?_
        simpa using ha
    · cases h
  split at h
  · -- kind 3: no rainbow 3-term progression
    split at h
    · cases h
      rename_i hv
      obtain ⟨⟨⟨⟨⟨⟨⟨hd, hn⟩, h3⟩, h4⟩, h5⟩, h34⟩, h35⟩, h45⟩ := hv
      have bits : ∀ u, (Nat.lor (Nat.lor (bit (f1 * R + f3)) (bit ((f1 + f2) * R + f4)))
          (bit ((f1 + 2 * f2) * R + f5))).testBit u =
          (decide (f1 * R + f3 = u) || decide ((f1 + f2) * R + f4 = u) ||
            decide ((f1 + 2 * f2) * R + f5 = u)) := by
        intro u; rw [testBit_lor', testBit_lor', testBit_bit, testBit_bit, testBit_bit]
      by_cases e0 : col f1 = f3
      · by_cases e1 : col (f1 + f2) = f4
        · by_cases e2 : col (f1 + 2 * f2) = f5
          · exact absurd ⟨by omega, by omega, by omega⟩ (hcol.rb f1 f2 hd hn)
          · refine holds_neg (i := f1 + 2 * f2) (c := f5) h5 ?_ e2
            show (Nat.lor (Nat.lor _ _) _).testBit _ = true
            rw [bits]; simp
        · refine holds_neg (i := f1 + f2) (c := f4) h4 ?_ e1
          show (Nat.lor (Nat.lor _ _) _).testBit _ = true
          rw [bits]; simp
      · refine holds_neg (i := f1) (c := f3) h3 ?_ e0
        show (Nat.lor (Nat.lor _ _) _).testBit _ = true
        rw [bits]; simp
    · cases h
  split at h
  · -- kind 4: colour 0 at position 0
    split at h
    · cases h
      rename_i hR0
      refine holds_pos (i := 0) (c := 0) hR0 ?_ hcol.zero
      show (1 : Nat).testBit (0 * R + 0) = true
      simp
    · cases h
  split at h
  · -- kind 5: first-occurrence order
    split at h
    · cases h
      rename_i hv
      obtain ⟨h1c, hcR⟩ := hv
      by_cases hci : col f1 = f2
      · obtain ⟨j, hj, hj'⟩ := hcol.pred f1 (by omega)
        refine holds_pos (i := j) (c := f2 - 1) (by omega) ?_ (by omega)
        show (Nat.shiftLeft (rep R f1) (f2 - 1)).testBit (j * R + (f2 - 1)) = true
        show ((rep R f1) <<< (f2 - 1)).testBit (j * R + (f2 - 1)) = true
        rw [Nat.testBit_shiftLeft]
        simp only [Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
        exact rep_bit R f1 j hj
      · refine holds_neg (i := f1) (c := f2) hcR ?_ hci
        show (bit (f1 * R + f2)).testBit _ = true
        rw [testBit_bit]; simp
    · cases h
  · cases h

/-- **Soundness for the GW CNF.** If the checker accepts a certificate, no colouring of the
positions `0, …, n - 1` has the properties `GoodPos n R l`. -/
theorem checkGw_sound {n R l : Nat} (steps : List Nat) (h : checkGw n R l steps = true)
    {col : Nat → Nat} (hcol : GoodPos n R l col) : False := by
  refine run_sound (σ := asg R col) ?_ steps .leaf 0 (good_leaf _) h
  intro db hdb hint c hc
  unfold gwSrc at hc
  cases hb : Nat.beq (Nat.land hint 1) 1
  · rw [hb, Bool.cond_false] at hc
    exact descCls_holds hcol _ hc
  · rw [hb, Bool.cond_true] at hc
    exact hdb _ _ hc

end GwExact
