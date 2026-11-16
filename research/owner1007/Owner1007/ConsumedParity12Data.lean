import NetHack.SokobanLinearPhases.Map12.Base
import Owner1007.ConsumedParity11
import NetHack.Sokoban.Generated.Soko12Potential
namespace Owner1007.ConsumedParity12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential
def crates : List Cell := NetHack.SokobanLinearPhases.Map12.cratesRegion0
def q (cell : Cell) : Int := if (cell/26+cell%26)%2=0 then 0 else 1
def difference (cell : Cell) : Int := q cell-p.boulder cell
def rowCheck (source : Cell) (dir : Dir) : Bool :=
 (pushTargets soko1_2.board source dir).all fun dest=>decide
   (dest≠source→(dest∈crates→(1+q dest-q source)%2=0) ∧
    (dest∈soko1_2.initial.holes→(1-p.hole dest-q source)%2=0))
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rows_checked : crates.all (fun source=>allDirs.all (rowCheck source))=true := by decide +kernel
theorem phase_checked : (List.range 18).all (fun phase=>
 (NetHack.SokobanLinearPhases.Map12.crates phase).all (fun c=>decide (c∈crates)))=true := by decide +kernel
def Left : List Cell := [108,158,159,186,187,210,213,237,238,263,265,318,371]
theorem initial_left_checked : Left.all (fun c=>decide (difference c%2=0))=true := by decide +kernel

theorem row (source dest : Cell) (dir : Dir) (member : source∈crates)
 (target : dest∈pushTargets soko1_2.board source dir) (different : dest≠source) :
 (dest∈crates→(1+q dest-q source)%2=0) ∧
 (dest∈soko1_2.initial.holes→(1-p.hole dest-q source)%2=0) := by
 have checked := List.all_eq_true.mp (List.all_eq_true.mp rows_checked source member) dir (Geometry.all_directions dir)
 exact of_decide_eq_true (List.all_eq_true.mp checked dest target) different
#print axioms rows_checked
#print axioms initial_left_checked
end Owner1007.ConsumedParity12
