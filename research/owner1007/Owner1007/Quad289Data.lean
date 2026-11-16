import Owner1007.RightPrice4
namespace Owner1007.Quad28912
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def locks : Fin 8 → List Cell
 | 0 => [210,211,237,263,289]
 | 1 => [236,263,289]
 | 2 => [210,236]
 | 3 => [210,211,237,262]
 | 4 => [236,262]
 | 5 => [210,211,236,237]
 | 6 => [262,263,289]
 | 7 => []
def pocket : Fin 8 → List Cell
 | 0 => [236,262,288]
 | 1 => [262,288]
 | 3 => [236]
 | 6 => [288]
 | _ => []
def region (i : Fin 8) : List Cell :=
 soko1_2.board.floor.filter fun c => !(locks i).contains c && !(pocket i).contains c
def credit : Fin 8 → Int | 0 => 5 | 1 => 3 | 2 => 3 | 3 => 3 | 4 => 3 | 5 => 3 | 6 => 1 | 7 => 0
def matrixNode (i : Fin 8) : Bool :=
 (region i).all fun hero => allDirs.all fun dir =>
  Corral11.walkCheck soko1_2.board locks region i hero dir &&
   PricedCorral.pushCheck soko1_2.board soko1_2.initial.holes p locks region credit i hero dir
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem debt_credit : ∀ i, credit i≤debtOf p (locks i) := by decide +kernel
end Owner1007.Quad28912

