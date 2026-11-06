/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem walk_player151 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 151 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨151,target,direction⟩ : WalkEdge)] else []) = [⟨151,137,.north⟩,⟨151,152,.east⟩,⟨151,150,.west⟩,⟨151,138,.northEast⟩,⟨151,136,.northWest⟩] := by decide
theorem walk_player152 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 152 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨152,target,direction⟩ : WalkEdge)] else []) = [⟨152,138,.north⟩,⟨152,151,.west⟩,⟨152,137,.northWest⟩] := by decide
theorem walk_player156 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 156 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨156,target,direction⟩ : WalkEdge)] else []) = [⟨156,142,.north⟩,⟨156,157,.east⟩,⟨156,143,.northEast⟩] := by decide
theorem walk_player157 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 157 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨157,target,direction⟩ : WalkEdge)] else []) = [⟨157,143,.north⟩,⟨157,156,.west⟩,⟨157,144,.northEast⟩,⟨157,142,.northWest⟩] := by decide
end NetHack.Sokoban41
