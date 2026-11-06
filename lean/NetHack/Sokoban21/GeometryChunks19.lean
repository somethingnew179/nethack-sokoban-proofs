/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks18
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player55 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 55 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨55,target,direction⟩ : WalkEdge)] else []) = [⟨55,35,.north⟩,⟨55,56,.east⟩,⟨55,75,.south⟩,⟨55,54,.west⟩,⟨55,36,.northEast⟩,⟨55,76,.southEast⟩,⟨55,74,.southWest⟩,⟨55,34,.northWest⟩] := by decide
theorem walk_player56 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 56 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨56,target,direction⟩ : WalkEdge)] else []) = [⟨56,36,.north⟩,⟨56,57,.east⟩,⟨56,76,.south⟩,⟨56,55,.west⟩,⟨56,37,.northEast⟩,⟨56,77,.southEast⟩,⟨56,75,.southWest⟩,⟨56,35,.northWest⟩] := by decide
theorem walk_player57 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 57 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨57,target,direction⟩ : WalkEdge)] else []) = [⟨57,37,.north⟩,⟨57,58,.east⟩,⟨57,77,.south⟩,⟨57,56,.west⟩,⟨57,38,.northEast⟩,⟨57,78,.southEast⟩,⟨57,76,.southWest⟩,⟨57,36,.northWest⟩] := by decide
theorem walk_player58 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 58 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨58,target,direction⟩ : WalkEdge)] else []) = [⟨58,38,.north⟩,⟨58,78,.south⟩,⟨58,57,.west⟩,⟨58,77,.southWest⟩,⟨58,37,.northWest⟩] := by decide
theorem walk_player61 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 61 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨61,target,direction⟩ : WalkEdge)] else []) = [⟨61,41,.north⟩,⟨61,62,.east⟩,⟨61,42,.northEast⟩,⟨61,82,.southEast⟩] := by decide
theorem walk_player62 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 62 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨62,target,direction⟩ : WalkEdge)] else []) = [⟨62,42,.north⟩,⟨62,82,.south⟩,⟨62,61,.west⟩,⟨62,43,.northEast⟩,⟨62,41,.northWest⟩] := by decide
theorem walk_player64 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 64 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨64,target,direction⟩ : WalkEdge)] else []) = [⟨64,44,.north⟩,⟨64,65,.east⟩,⟨64,84,.south⟩,⟨64,45,.northEast⟩,⟨64,85,.southEast⟩,⟨64,43,.northWest⟩] := by decide
theorem walk_player65 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 65 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨65,target,direction⟩ : WalkEdge)] else []) = [⟨65,45,.north⟩,⟨65,66,.east⟩,⟨65,85,.south⟩,⟨65,64,.west⟩,⟨65,84,.southWest⟩,⟨65,44,.northWest⟩] := by decide
end NetHack.Sokoban21
