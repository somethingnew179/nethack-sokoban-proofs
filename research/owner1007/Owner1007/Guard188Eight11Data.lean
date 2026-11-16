import Owner1007.UpperLocalPrice11
import Owner1007.Guard18811
namespace Owner1007.Guard188Eight11
open NetHack.Sokoban
def cells : List Cell := [188,189,190,164,138,112,187,191]
def cell (i : Fin 8) : Cell := cells[i.val]?.getD 0
def locks (i : Fin 8) : List Cell := [137,139,cell i]
def region (i : Fin 8) : List Cell :=
 if bound : i.val<6 then Guard18811.region ⟨i.val,bound⟩
 else (NetHack.SokobanLinearPhases.Map11.heroesRegion16).filter fun c => ![137,139,cell i].contains c
def paid (source : Cell) (dir : Dir) : Prop :=
 source=137 ∨ source=139 ∨ (source=187 ∧ dir=.west) ∨ (source=191 ∧ dir=.east)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique : ∀i, (locks i).Nodup := by decide +kernel
theorem size : ∀i, (locks i).length=3 := by decide +kernel
end Owner1007.Guard188Eight11
