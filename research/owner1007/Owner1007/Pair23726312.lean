import Owner1007.RightPrice4
namespace Owner1007.Pair23726312
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def pair : List Cell := [237,263]
def locks (i : Fin 2) : List Cell := if i.val=0 then pair else []
def region (i : Fin 2) : List Cell :=
  soko1_2.board.floor.filter fun c => !(locks i).contains c
def credit (i : Fin 2) : Int := if i.val=0 then 2 else 0
/-- This two-phase relaxation does not certify the proposed extra2 ticket. -/
theorem matrix_rejected : PricedCorral.check soko1_2.board soko1_2.initial.holes p
    locks region credit=false := by decide +kernel
theorem east_free :
 1+p.boulder 238-p.boulder 237=0 ∧ 1+p.boulder 264-p.boulder 263=0 := by decide +kernel
#print axioms matrix_rejected
#print axioms east_free
end Owner1007.Pair23726312
