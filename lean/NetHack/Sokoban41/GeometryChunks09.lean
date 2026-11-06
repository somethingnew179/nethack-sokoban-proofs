/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem push_source123 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 123 direction).map (computedPushEdge 123 direction)) = [⟨123,137,109,109,.north,2,13,false,false⟩,⟨123,122,124,124,.east,13,13,false,true⟩,⟨123,109,137,137,.south,0,13,false,false⟩,⟨123,124,122,122,.west,0,13,false,false⟩] := by decide
theorem push_source124 : checkedDirs.flatMap (fun direction =>
    (pushTargets soko4_1.board 124 direction).map (computedPushEdge 124 direction)) = [⟨124,138,110,110,.north,1,1,true,true⟩,⟨124,110,138,138,.south,1,1,true,true⟩] := by decide
theorem walk_player15 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 15 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨15,target,direction⟩ : WalkEdge)] else []) = [⟨15,16,.east⟩,⟨15,29,.south⟩,⟨15,30,.southEast⟩] := by decide
theorem walk_player16 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 16 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨16,target,direction⟩ : WalkEdge)] else []) = [⟨16,17,.east⟩,⟨16,30,.south⟩,⟨16,15,.west⟩,⟨16,31,.southEast⟩,⟨16,29,.southWest⟩] := by decide
theorem walk_player17 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 17 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨17,target,direction⟩ : WalkEdge)] else []) = [⟨17,18,.east⟩,⟨17,31,.south⟩,⟨17,16,.west⟩,⟨17,32,.southEast⟩,⟨17,30,.southWest⟩] := by decide
theorem walk_player18 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 18 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨18,target,direction⟩ : WalkEdge)] else []) = [⟨18,32,.south⟩,⟨18,17,.west⟩,⟨18,31,.southWest⟩] := by decide
theorem walk_player23 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 23 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨23,target,direction⟩ : WalkEdge)] else []) = [⟨23,24,.east⟩,⟨23,37,.south⟩,⟨23,38,.southEast⟩] := by decide
theorem walk_player24 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 24 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨24,target,direction⟩ : WalkEdge)] else []) = [⟨24,25,.east⟩,⟨24,38,.south⟩,⟨24,23,.west⟩,⟨24,39,.southEast⟩,⟨24,37,.southWest⟩] := by decide
end NetHack.Sokoban41
