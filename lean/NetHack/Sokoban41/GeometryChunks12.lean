/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem walk_player51 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 51 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨51,target,direction⟩ : WalkEdge)] else []) = [⟨51,37,.north⟩,⟨51,52,.east⟩,⟨51,50,.west⟩,⟨51,38,.northEast⟩,⟨51,66,.southEast⟩] := by decide
theorem walk_player52 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 52 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨52,target,direction⟩ : WalkEdge)] else []) = [⟨52,38,.north⟩,⟨52,53,.east⟩,⟨52,66,.south⟩,⟨52,51,.west⟩,⟨52,39,.northEast⟩,⟨52,67,.southEast⟩,⟨52,37,.northWest⟩] := by decide
theorem walk_player53 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 53 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨53,target,direction⟩ : WalkEdge)] else []) = [⟨53,39,.north⟩,⟨53,67,.south⟩,⟨53,52,.west⟩,⟨53,66,.southWest⟩,⟨53,38,.northWest⟩] := by decide
theorem walk_player57 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 57 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨57,target,direction⟩ : WalkEdge)] else []) = [⟨57,43,.north⟩,⟨57,58,.east⟩,⟨57,44,.northEast⟩] := by decide
theorem walk_player58 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 58 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨58,target,direction⟩ : WalkEdge)] else []) = [⟨58,44,.north⟩,⟨58,57,.west⟩,⟨58,45,.northEast⟩,⟨58,43,.northWest⟩] := by decide
theorem walk_player62 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 62 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨62,target,direction⟩ : WalkEdge)] else []) = [⟨62,48,.north⟩,⟨62,49,.northEast⟩,⟨62,47,.northWest⟩] := by decide
theorem walk_player66 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 66 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨66,target,direction⟩ : WalkEdge)] else []) = [⟨66,52,.north⟩,⟨66,67,.east⟩,⟨66,80,.south⟩,⟨66,53,.northEast⟩,⟨66,51,.northWest⟩] := by decide
theorem walk_player67 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 67 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨67,target,direction⟩ : WalkEdge)] else []) = [⟨67,53,.north⟩,⟨67,66,.west⟩,⟨67,80,.southWest⟩,⟨67,52,.northWest⟩] := by decide
end NetHack.Sokoban41
