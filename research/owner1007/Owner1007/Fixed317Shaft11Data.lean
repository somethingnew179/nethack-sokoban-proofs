import Owner1007.FastCorral11
import Owner1007.ZeroWord11
namespace Owner1007.Fixed317Shaft11
open NetHack.Sokoban
def H := NetHack.SokobanLinearPhases.Map11.heroesRegion16
def cells : List Cell := [209,210,211,212,213,239,265,291]
def locks (i : Fin 8) : List Cell := [317,cells[i.val]!]
def region (i : Fin 8) : List Cell :=
 if i.val<4 ∨ i.val=7 then H.filter fun c=>c≠317 &&c≠cells[i.val]!
 else H.filter fun c=>c≠317 &&c≠cells[i.val]! && (c<239 || 12≤c%26 || (i.val≥5 &&c=213) || (i.val≥6 &&c=239))
def paid (source : Cell) (dir : Dir) : Prop :=
 source=317 ∨(source=213 ∧dir=.east) ∨(source=291 ∧(dir=.east∨dir=.west∨dir=.south))
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
end Owner1007.Fixed317Shaft11
