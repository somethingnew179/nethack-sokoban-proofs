import Owner1007.FastCorral11
import Owner1007.ZeroWord11
namespace Owner1007.Parked18811
open NetHack.Sokoban
def patterns : List (List Cell) :=
  [[137,139,164,189],[137,139,138,189],[137,139,112,189],
   [137,139,164,190],[137,139,138,190],[137,139,112,190],
   [137,139,138,164],[137,139,112,164],[137,139,112,138]]
def locks (i : Fin 9) : List Cell := patterns[i.val]?.getD []
def B : List Cell := ZeroWord11.lowerTwo
def remove (box : Cell) : List Cell := B.filter fun c => !(decide (c=box))
def region (i : Fin 9) : List Cell :=
  match i.val with
  | 0 => remove 189
  | 1 => remove 189 ++ [164]
  | 2 => remove 189 ++ [164,138]
  | 3 => remove 190
  | 4 => remove 190
  | 5 => remove 190
  | 6 => B
  | 7 => B
  | _ => B ++ [164]
def paid (source : Cell) (dir : Dir) : Prop :=
  (source=189 ∧ dir=.west) ∨ (source=190 ∧ (dir=.east ∨ dir=.west)) ∨
  (source=137 ∧ dir=.west) ∨ (source=139 ∧ dir=.east) ∨
  (source=112 ∧ dir=.east) ∨ (source=138 ∧ (dir=.east ∨ dir=.west))
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
end Owner1007.Parked18811
