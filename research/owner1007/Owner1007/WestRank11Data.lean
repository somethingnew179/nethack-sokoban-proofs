import Owner1007.FastCorral11
import Owner1007.PairPath11
import Owner1007.CutStrict11
namespace Owner1007.WestRank11
open NetHack.Sokoban NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
def gates : List Cell := [136,137,138,139,136,137,138,139,164,136,137,138,139,164,190]
def markers : List Cell := [164,164,164,164,190,190,190,190,190,216,216,216,216,216,216]
def patterns : List (List Cell) := [[136,191,164],[137,191,164],[138,191,164],[139,191,164],[136,191,190],[137,191,190],[138,191,190],[139,191,190],[164,191,190],[136,191,216],[137,191,216],[138,191,216],[139,191,216],[164,191,216],[190,191,216]]
def gate (i : Fin 15) : Cell := gates[i.val]?.getD 0
def marker (i : Fin 15) : Cell := markers[i.val]?.getD 0
def locks (i : Fin 15) : List Cell := patterns[i.val]?.getD []
def rank (i : Fin 15) : Int := if gate i=136 ∨ gate i=139 then 2 else 0
def base (i : Fin 15) : Fin 9 :=
 if gate i=138 then 1 else if gate i=164 then 2 else if gate i=190 then 3
 else if marker i=164 then 2 else if marker i=190 then 3 else 4
def region (i : Fin 15) : List Cell := (PairPath11.region (base i)).filter fun c => !decide (c=gate i)
def paid (source : Cell) (dir : Dir) : Prop :=
 source=191 ∨ source=216 ∨ (source=136 ∧ dir=.west) ∨ (source=139 ∧ dir=.east)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
instance (source : Cell) (dir : Dir) : Decidable (CutActor11.Exit source dir) := by unfold CutActor11.Exit; infer_instance
def refinementCheck (i : Fin 15) : Bool := (locks i).all fun source => allDirs.all fun dir =>
 match advance soko1_1.board source dir.opposite with
 | none => true
 | some hero => if hero∈region i then (List.finRange 15).all fun j =>
   (pushTargets soko1_1.board source dir).all fun dest => decide
    (dir.diagonal=false → ¬paid source dir → pushTargets soko1_1.board source dir=[dest] →
     dest∉soko1_1.initial.holes → locks j⊆dest::(locks i).erase source → source∈region j →
     update [marker i] (.push source (.stay dest))=[marker j] ∧
     (rank j≤rank i ∨ (rank j≤rank i+2 ∧ CutActor11.Exit source dir)))
  else true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique : ∀i, (locks i).Nodup := by decide +kernel
theorem size : ∀i, (locks i).length=3 := by decide +kernel
theorem marker_inside : ∀i, marker i∈locks i := by decide +kernel
#print axioms unique
#print axioms size
#print axioms marker_inside
end Owner1007.WestRank11
