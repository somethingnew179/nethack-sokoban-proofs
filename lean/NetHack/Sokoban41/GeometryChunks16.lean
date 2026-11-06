/- Stage-only soko4-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban41.GeometryChunks15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Sokoban41
open NetHack.Sokoban
theorem walk_player124 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 124 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨124,target,direction⟩ : WalkEdge)] else []) = [⟨124,110,.north⟩,⟨124,138,.south⟩,⟨124,123,.west⟩,⟨124,137,.southWest⟩,⟨124,109,.northWest⟩] := by decide
theorem walk_player128 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 128 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨128,target,direction⟩ : WalkEdge)] else []) = [⟨128,114,.north⟩,⟨128,142,.south⟩,⟨128,143,.southEast⟩] := by decide
theorem walk_player134 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 134 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨134,target,direction⟩ : WalkEdge)] else []) = [⟨134,120,.north⟩,⟨134,135,.east⟩,⟨134,148,.south⟩,⟨134,121,.northEast⟩,⟨134,149,.southEast⟩,⟨134,147,.southWest⟩] := by decide
theorem walk_player135 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 135 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨135,target,direction⟩ : WalkEdge)] else []) = [⟨135,121,.north⟩,⟨135,136,.east⟩,⟨135,149,.south⟩,⟨135,134,.west⟩,⟨135,122,.northEast⟩,⟨135,150,.southEast⟩,⟨135,148,.southWest⟩,⟨135,120,.northWest⟩] := by decide
theorem walk_player136 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 136 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨136,target,direction⟩ : WalkEdge)] else []) = [⟨136,122,.north⟩,⟨136,137,.east⟩,⟨136,150,.south⟩,⟨136,135,.west⟩,⟨136,123,.northEast⟩,⟨136,151,.southEast⟩,⟨136,149,.southWest⟩,⟨136,121,.northWest⟩] := by decide
theorem walk_player137 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 137 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨137,target,direction⟩ : WalkEdge)] else []) = [⟨137,123,.north⟩,⟨137,138,.east⟩,⟨137,151,.south⟩,⟨137,136,.west⟩,⟨137,124,.northEast⟩,⟨137,152,.southEast⟩,⟨137,150,.southWest⟩,⟨137,122,.northWest⟩] := by decide
theorem walk_player138 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 138 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨138,target,direction⟩ : WalkEdge)] else []) = [⟨138,124,.north⟩,⟨138,152,.south⟩,⟨138,137,.west⟩,⟨138,151,.southWest⟩,⟨138,123,.northWest⟩] := by decide
theorem walk_player142 : checkedDirs.flatMap (fun direction =>
    match advance soko4_1.board 142 direction with
    | none => []
    | some target => if soko4_1.board.floor.contains target then [(⟨142,target,direction⟩ : WalkEdge)] else []) = [⟨142,128,.north⟩,⟨142,143,.east⟩,⟨142,156,.south⟩,⟨142,157,.southEast⟩] := by decide
end NetHack.Sokoban41
