/- Finite involutive cell permutations, extended by identity outside the board.
The table is proposed data; its boundedness and involution are kernel checked.
No generic arithmetic claim about an intuitive reflection is assumed. -/
import NetHack.Sokoban.Model

namespace NetHack.Sokoban.Symmetry

structure CellPermutation where
  apply : Cell → Cell
  involutive : ∀ cell, apply (apply cell) = cell

namespace CellPermutation

theorem injective (perm : CellPermutation) {first second : Cell}
    (same : perm.apply first = perm.apply second) : first = second := by
  have twice := congrArg perm.apply same
  simpa only [perm.involutive] using twice

theorem list_involutive (perm : CellPermutation) (cells : List Cell) :
    (cells.map perm.apply).map perm.apply = cells := by
  induction cells with
  | nil => rfl
  | cons head tail ih => simp [perm.involutive, ih]

theorem contains_map (perm : CellPermutation) (cells : List Cell) (cell : Cell) :
    (cells.map perm.apply).contains (perm.apply cell) = cells.contains cell := by
  apply Bool.eq_iff_iff.mpr
  change ((cells.map perm.apply).contains (perm.apply cell) = true ↔ cells.contains cell = true)
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨original, member, same⟩
    have equal := perm.injective same
    simpa [equal] using member
  · intro member
    exact ⟨cell, member, rfl⟩

theorem erase_map (perm : CellPermutation) (cells : List Cell) (cell : Cell) :
    (cells.map perm.apply).erase (perm.apply cell) = (cells.erase cell).map perm.apply := by
  induction cells with
  | nil => rfl
  | cons head tail ih =>
    by_cases same : head = cell
    · subst head
      simp
    · have different : perm.apply head ≠ perm.apply cell := fun equal => same (perm.injective equal)
      simp [List.erase_cons, same, Ne.symm same, different, Ne.symm different, ih]

end CellPermutation

def tableMap (table : List Cell) (cell : Cell) : Cell := table[cell]?.getD cell

def permutationCheck (table : List Cell) : Bool :=
  (List.range table.length).all fun cell =>
    decide (tableMap table cell < table.length ∧ tableMap table (tableMap table cell) = cell)

theorem tableMap_outside (table : List Cell) (cell : Cell) (outside : table.length ≤ cell) :
    tableMap table cell = cell := by
  have absent : table[cell]? = none := List.getElem?_eq_none_iff.mpr outside
  simp [tableMap, absent]

theorem permutationCheck_inside (table : List Cell) (checked : permutationCheck table = true)
    (cell : Cell) (inside : cell < table.length) :
    tableMap table cell < table.length ∧ tableMap table (tableMap table cell) = cell :=
  of_decide_eq_true (List.all_eq_true.mp checked cell (List.mem_range.mpr inside))

def ofTable (table : List Cell) (checked : permutationCheck table = true) : CellPermutation := {
  apply := tableMap table
  involutive := by
    intro cell
    by_cases inside : cell < table.length
    · exact (permutationCheck_inside table checked cell inside).2
    · have outside : table.length ≤ cell := Nat.le_of_not_gt inside
      rw [tableMap_outside table cell outside, tableMap_outside table cell outside] }

end NetHack.Sokoban.Symmetry
