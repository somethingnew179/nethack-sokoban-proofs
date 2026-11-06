/- Stage-only exact soko2-1 geometry/facts; small ordinary kernel checks. -/
import NetHack.Sokoban21.GeometryChunks15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban21
open NetHack.Sokoban
theorem walk_player23 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 23 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨23,target,direction⟩ : WalkEdge)] else []) = [⟨23,24,.east⟩,⟨23,43,.south⟩,⟨23,22,.west⟩,⟨23,44,.southEast⟩,⟨23,42,.southWest⟩] := by decide
theorem walk_player24 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 24 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨24,target,direction⟩ : WalkEdge)] else []) = [⟨24,25,.east⟩,⟨24,44,.south⟩,⟨24,23,.west⟩,⟨24,45,.southEast⟩,⟨24,43,.southWest⟩] := by decide
theorem walk_player25 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 25 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨25,target,direction⟩ : WalkEdge)] else []) = [⟨25,26,.east⟩,⟨25,45,.south⟩,⟨25,24,.west⟩,⟨25,44,.southWest⟩] := by decide
theorem walk_player26 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 26 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨26,target,direction⟩ : WalkEdge)] else []) = [⟨26,27,.east⟩,⟨26,25,.west⟩,⟨26,47,.southEast⟩,⟨26,45,.southWest⟩] := by decide
theorem walk_player27 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 27 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨27,target,direction⟩ : WalkEdge)] else []) = [⟨27,28,.east⟩,⟨27,47,.south⟩,⟨27,26,.west⟩,⟨27,48,.southEast⟩] := by decide
theorem walk_player28 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 28 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨28,target,direction⟩ : WalkEdge)] else []) = [⟨28,48,.south⟩,⟨28,27,.west⟩,⟨28,47,.southWest⟩] := by decide
theorem walk_player30 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 30 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨30,target,direction⟩ : WalkEdge)] else []) = [⟨30,31,.east⟩,⟨30,50,.south⟩] := by decide
theorem walk_player31 : checkedDirs.flatMap (fun direction =>
    match advance soko2_1.board 31 direction with
    | none => []
    | some target => if soko2_1.board.floor.contains target then [(⟨31,target,direction⟩ : WalkEdge)] else []) = [⟨31,32,.east⟩,⟨31,30,.west⟩,⟨31,52,.southEast⟩,⟨31,50,.southWest⟩] := by decide
end NetHack.Sokoban21
