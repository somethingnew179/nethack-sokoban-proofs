/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks21
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player90 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 90 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨90,target,direction⟩ : WalkEdge)] else []) = [⟨90,70,.north⟩,⟨90,110,.south⟩,⟨90,71,.northEast⟩,⟨90,111,.southEast⟩,⟨90,109,.southWest⟩] := by decide
theorem walk_player92 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 92 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨92,target,direction⟩ : WalkEdge)] else []) = [⟨92,72,.north⟩,⟨92,112,.south⟩,⟨92,111,.southWest⟩,⟨92,71,.northWest⟩] := by decide
theorem walk_player94 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 94 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨94,target,direction⟩ : WalkEdge)] else []) = [⟨94,74,.north⟩,⟨94,95,.east⟩,⟨94,114,.south⟩,⟨94,75,.northEast⟩,⟨94,115,.southEast⟩] := by decide
theorem walk_player95 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 95 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨95,target,direction⟩ : WalkEdge)] else []) = [⟨95,75,.north⟩,⟨95,96,.east⟩,⟨95,115,.south⟩,⟨95,94,.west⟩,⟨95,76,.northEast⟩,⟨95,116,.southEast⟩,⟨95,114,.southWest⟩,⟨95,74,.northWest⟩] := by decide
theorem walk_player96 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 96 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨96,target,direction⟩ : WalkEdge)] else []) = [⟨96,76,.north⟩,⟨96,97,.east⟩,⟨96,116,.south⟩,⟨96,95,.west⟩,⟨96,77,.northEast⟩,⟨96,117,.southEast⟩,⟨96,115,.southWest⟩,⟨96,75,.northWest⟩] := by decide
theorem walk_player97 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 97 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨97,target,direction⟩ : WalkEdge)] else []) = [⟨97,77,.north⟩,⟨97,98,.east⟩,⟨97,117,.south⟩,⟨97,96,.west⟩,⟨97,78,.northEast⟩,⟨97,118,.southEast⟩,⟨97,116,.southWest⟩,⟨97,76,.northWest⟩] := by decide
theorem walk_player98 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 98 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨98,target,direction⟩ : WalkEdge)] else []) = [⟨98,78,.north⟩,⟨98,118,.south⟩,⟨98,97,.west⟩,⟨98,117,.southWest⟩,⟨98,77,.northWest⟩] := by decide
theorem walk_player101 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 101 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨101,target,direction⟩ : WalkEdge)] else []) = [⟨101,102,.east⟩,⟨101,121,.south⟩,⟨101,82,.northEast⟩,⟨101,122,.southEast⟩] := by decide
end NetHack.Sokoban21
