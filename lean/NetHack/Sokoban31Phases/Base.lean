import NetHack.Sokoban.HazardPhases
import NetHack.Sokoban.Maps
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban31Phases
open NetHack.Sokoban NetHack.Sokoban.HazardPhases
def heroes (phase : Nat) : List Cell := soko3_1.board.floor.filter fun cell => decide (cell % 29 < 12 ∨ (302 ≤ cell ∧ cell < 302 + phase))
def crates (_phase : Nat) : List Cell := soko3_1.board.floor.filter fun cell => decide (cell % 29 < 12 ∧ cell ≠ 301)
end NetHack.Sokoban31Phases
