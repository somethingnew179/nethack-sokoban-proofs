/- Finite geometry certificate, extended to every Nat cell by the explicit
identity-outside table convention. This closes all malformed-input cases. -/
import NetHack.Sokoban.Symmetry.Trace

namespace NetHack.Sokoban.Symmetry

def advanceCheck (board : Board) (cells : CellPermutation) (directions : DirectionPermutation) : Bool :=
  (List.range (board.width * board.height)).all fun cell =>
    allDirs.all fun direction => decide (
      advance (mapBoard cells board) (cells.apply cell) (directions.apply direction) =
        (advance board cell direction).map cells.apply)

theorem allDirs_mem (direction : Dir) : direction ∈ allDirs := by
  cases direction <;> simp [allDirs, cardinalDirs]

def finiteIsomorphism (board : Board) (table : List Cell)
    (permutationChecked : permutationCheck table = true)
    (length : table.length = board.width * board.height)
    (directions : DirectionPermutation)
    (geometryChecked : advanceCheck board (ofTable table permutationChecked) directions = true) :
    BoardIsomorphism board := {
  cells := ofTable table permutationChecked
  directions := directions
  advance := by
    intro cell direction
    by_cases inside : cell < board.width * board.height
    · exact of_decide_eq_true (List.all_eq_true.mp
        (List.all_eq_true.mp geometryChecked cell (List.mem_range.mpr inside))
        direction (allDirs_mem direction))
    · have outside : board.width * board.height ≤ cell := Nat.le_of_not_gt inside
      have tableOutside : table.length ≤ cell := by simpa only [length] using outside
      have identity : (ofTable table permutationChecked).apply cell = cell :=
        tableMap_outside table cell tableOutside
      simp only [identity, advance, board_width, board_height]
      simp only [outside, or_true, ↓reduceIte, Option.map_none] }

end NetHack.Sokoban.Symmetry
