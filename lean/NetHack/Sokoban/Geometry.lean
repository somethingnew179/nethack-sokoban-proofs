/- Finite geometry certificates for the actual source boards. The checker
and its soundness theorem avoid assuming that flattened indices behave like
an unbounded grid; edges, opposite directions and row boundaries are checked. -/
import NetHack.Sokoban.Maps

namespace NetHack.Sokoban.Geometry

def reverseCheck (board : Board) : Bool :=
  board.floor.all fun player => allDirs.all fun direction =>
    match advance board player direction with
    | none => true
    | some source => decide (advance board source direction.opposite = some player)

theorem all_directions (direction : Dir) : direction ∈ allDirs := by
  cases direction <;> simp [allDirs, cardinalDirs]

theorem reverseCheck_sound (board : Board) (checked : reverseCheck board = true)
    (player : Cell) (floor : player ∈ board.floor) (direction : Dir) (source : Cell)
    (adjacent : advance board player direction = some source) :
    advance board source direction.opposite = some player := by
  simp only [reverseCheck, List.all_eq_true] at checked
  have edge := checked player floor direction (all_directions direction)
  simpa [adjacent] using edge

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem soko4_2_reverse_checked : reverseCheck soko4_2.board = true := by decide

theorem soko4_2_reverse (player : Cell) (floor : player ∈ soko4_2.board.floor)
    (direction : Dir) (source : Cell)
    (adjacent : advance soko4_2.board player direction = some source) :
    advance soko4_2.board source direction.opposite = some player :=
  reverseCheck_sound soko4_2.board soko4_2_reverse_checked player floor direction source adjacent

end NetHack.Sokoban.Geometry
