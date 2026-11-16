import Owner1007.RightPrice4
namespace Owner1007.Residual29012
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def locks : Fin 6 → List Cell
 | 0 => [236,237,263,290]
 | 1 => [262,263,290]
 | 2 => [236,263,289]
 | 3 => [262,263,289]
 | 4 => [236,262]
 | 5 => []
def pocket : Fin 6 → List Cell
 | 0 => [262,288,289]
 | 1 => [288,289]
 | 2 => [262,288]
 | 3 => [288]
 | _ => []
def region (i : Fin 6) : List Cell :=
 soko1_2.board.floor.filter fun c => !(locks i).contains c && !(pocket i).contains c
def credit : Fin 6 → Int | 0 => 5 | 1 => 3 | 2 => 3 | 3 => 1 | 4 => 3 | 5 => 0
def matrixNode (i : Fin 6) : Bool :=
 (region i).all fun hero => allDirs.all fun dir =>
  Corral11.walkCheck soko1_2.board locks region i hero dir &&
   PricedCorral.pushCheck soko1_2.board soko1_2.initial.holes p locks region credit i hero dir
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem debt_credit : ∀ i, credit i≤debtOf p (locks i) := by decide +kernel
end Owner1007.Residual29012

