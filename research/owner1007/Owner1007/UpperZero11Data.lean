import Owner1007.FastCorral11
import Owner1007.ZeroWord11
import Owner1007.ShaftCorral11
namespace Owner1007.UpperZero11
open NetHack.Sokoban
def patterns : List (List Cell) :=
  [[137,139,191],[138,139,191],[139,164,191],[139,190,191],[139,191,216],
   [137,138,191],[137,164,191],[137,190,191],[137,191,216],
   [138,191,216],[164,191,216],[190,191,216],
   [137,139,190],[137,139,164],[137,139,138],[137,139,112],
   [138,164,191],[138,190,191],[164,190,191]]
def locks (i : Fin 19) : List Cell := patterns[i.val]?.getD []
def H : List Cell := NetHack.SokobanLinearPhases.Map11.heroesRegion16
def U : List Cell := ShaftCorral11.region ⟨0,by decide⟩
def B : List Cell := ZeroWord11.lowerTwo
def without (cells blocked : List Cell) : List Cell := cells.filter fun c => !blocked.contains c
def region (i : Fin 19) : List Cell :=
  match i.val with
  | 0 => without H [137,139,191]
  | 1 => without U [138,139,164]
  | 2 => without U [139,164]
  | 3 => without U [139]
  | 4 => without H [139,191,192,193,194,216,217,218,219,220]
  | 5 => without U [137,138,164]
  | 6 => without U [137,164]
  | 7 => without U [137]
  | 8 => without H [137,191,192,193,194,216,217,218,219,220]
  | 9 => without U [138,164]
  | 10 => without U [164]
  | 11 => U
  | 12 => without B [190]
  | 13 => B
  | 14 => B ++ [164]
  | 15 => B ++ [164,138]
  | 16 => without U [138,164]
  | 17 => without U [138,164]
  | _ => without U [164]
def paid (source : Cell) (dir : Dir) : Prop :=
  (source=137 ∧ dir=.west) ∨ (source=139 ∧ dir=.east) ∨
  (source=191 ∧ dir=.east) ∨ (source=138 ∧ (dir=.east ∨ dir=.west)) ∨
  (source=190 ∧ (dir=.east ∨ dir=.west)) ∨ (source=216 ∧ dir=.east)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
end Owner1007.UpperZero11
