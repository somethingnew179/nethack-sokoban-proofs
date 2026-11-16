import Owner1007.Gate265Transport11Data
import Owner1007.FastCorral11
namespace Owner1007.Gate265Above11
open NetHack.Sokoban
def locks (i : Fin 2) : List Cell := if i.val=0 then [264,265,266] else [264,266,291]
def region (i : Fin 2) : List Cell := if i.val=0 then Gate265Transport11.upper else 265::Gate265Transport11.upper
def paid (source : Cell) (dir : Dir) : Prop := source=264∨source=266∨(source=291∧dir=.south)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
def Shape (source : Cell) (dir : Dir) : Prop :=
 (source=264∧dir=.west)∨(source=266∧dir=.east)∨(source=291∧dir=.south)
instance (source : Cell) (dir : Dir) : Decidable (Shape source dir) := by unfold Shape;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem unique (i : Fin 2) : (locks i).Nodup := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1 := by omega
 rcases choices with rfl|rfl
 ·change ([264,265,266] : List Cell).Nodup;decide +kernel
 ·change ([264,266,291] : List Cell).Nodup;decide +kernel
theorem size (i : Fin 2) : (locks i).length=3 := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1 := by omega
 rcases choices with rfl|rfl <;> rfl
theorem floor (i : Fin 2) : region i⊆soko1_1.board.floor := by
 obtain ⟨i,bound⟩ := i
 have choices : i=0∨i=1 := by omega
 rcases choices with rfl|rfl
 ·change Gate265Transport11.upper⊆soko1_1.board.floor;decide +kernel
 ·change 265::Gate265Transport11.upper⊆soko1_1.board.floor;decide +kernel
end Owner1007.Gate265Above11
