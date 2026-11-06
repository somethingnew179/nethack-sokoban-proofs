/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player32 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 32 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨32,target,direction⟩ : WalkEdge)] else []) = [⟨32,52,.south⟩,⟨32,31,.west⟩] := by decide
theorem walk_player34 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 34 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨34,target,direction⟩ : WalkEdge)] else []) = [⟨34,35,.east⟩,⟨34,54,.south⟩,⟨34,55,.southEast⟩] := by decide
theorem walk_player35 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 35 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨35,target,direction⟩ : WalkEdge)] else []) = [⟨35,36,.east⟩,⟨35,55,.south⟩,⟨35,34,.west⟩,⟨35,56,.southEast⟩,⟨35,54,.southWest⟩] := by decide
theorem walk_player36 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 36 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨36,target,direction⟩ : WalkEdge)] else []) = [⟨36,37,.east⟩,⟨36,56,.south⟩,⟨36,35,.west⟩,⟨36,57,.southEast⟩,⟨36,55,.southWest⟩] := by decide
theorem walk_player37 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 37 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨37,target,direction⟩ : WalkEdge)] else []) = [⟨37,38,.east⟩,⟨37,57,.south⟩,⟨37,36,.west⟩,⟨37,58,.southEast⟩,⟨37,56,.southWest⟩] := by decide
theorem walk_player38 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 38 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨38,target,direction⟩ : WalkEdge)] else []) = [⟨38,58,.south⟩,⟨38,37,.west⟩,⟨38,57,.southWest⟩] := by decide
theorem walk_player41 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 41 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨41,target,direction⟩ : WalkEdge)] else []) = [⟨41,21,.north⟩,⟨41,42,.east⟩,⟨41,61,.south⟩,⟨41,22,.northEast⟩,⟨41,62,.southEast⟩] := by decide
theorem walk_player42 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 42 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨42,target,direction⟩ : WalkEdge)] else []) = [⟨42,22,.north⟩,⟨42,43,.east⟩,⟨42,62,.south⟩,⟨42,41,.west⟩,⟨42,23,.northEast⟩,⟨42,61,.southWest⟩,⟨42,21,.northWest⟩] := by decide
end NetHack.Sokoban21
