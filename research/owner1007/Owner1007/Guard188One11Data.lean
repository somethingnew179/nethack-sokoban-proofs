import Owner1007.FastCorral11
import Owner1007.ZeroWord11
import Owner1007.PairPath11
import Owner1007.Guard188Actor11
namespace Owner1007.Guard188One11
open NetHack.Sokoban
def cells : List Cell := [188,189,190,164,138,112]
def cell (i : Fin 6) : Cell := cells[i.val]?.getD 0
def locks (i : Fin 6) : List Cell := [139,cell i]
def H : List Cell := NetHack.SokobanLinearPhases.Map11.heroesRegion16
def B : List Cell := ZeroWord11.lowerTwo
def without (cells blocked : List Cell) : List Cell := cells.filter fun c => !blocked.contains c
def region (i : Fin 6) : List Cell :=
 match i.val with
 | 0 => without H [139,188]
 | 1 => without H [139,189]
 | 2 => without B [190]
 | 3 => B
 | 4 => B ++ [164]
 | _ => PairPath11.region ⟨8,by decide⟩
def actorPaid (source : Cell) (dir : Dir) : Prop :=
 Guard188Actor11.Exit source dir ∨ (source=112 ∧ dir=.east)
instance (source : Cell) (dir : Dir) : Decidable (actorPaid source dir) := by
 unfold actorPaid Guard188Actor11.Exit
 infer_instance
def paid (source : Cell) (dir : Dir) : Prop := source=139 ∨ actorPaid source dir
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance

end Owner1007.Guard188One11
