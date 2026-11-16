import Owner1007.Row19019111
namespace Owner1007.LeftFourLane11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
def words : List (Cell×Cell) := [(184,185),(184,186),(184,187),(184,188),(184,189),(184,190),(185,186),(185,187),(185,188),(185,189),(185,190),(186,187),(186,188),(186,189),(186,190),(187,188),(187,189),(187,190),(188,189),(188,190),(189,190)]
def left (i : Fin 21) : Cell := (words.getD i.val (184,185)).1
def right (i : Fin 21) : Cell := (words.getD i.val (184,185)).2
def locks (i : Fin 21) : List Cell := [left i,right i]
def region (i : Fin 21) : List Cell :=
 (if right i=190 then Row19019111.region 0++[191] else LeftPair11.H).filter fun c=>!(locks i).contains c
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=184∧dir=.west)∨(source=190∧(dir=.north∨dir=.east))
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
end Owner1007.LeftFourLane11
