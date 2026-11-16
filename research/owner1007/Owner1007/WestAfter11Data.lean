import Owner1007.FastCorral11
import Owner1007.ShaftCorral11
import Owner1007.ZeroWord11
namespace Owner1007.WestAfter11
open NetHack.Sokoban
def patterns : List (List Cell) := [[137,191,216],[138,191,216],[164,191,216],[190,191,216]]
def locks (i : Fin 4) : List Cell := patterns[i.val]?.getD []
def U : List Cell := ShaftCorral11.region ⟨0,by decide⟩
def region (i : Fin 4) : List Cell :=
  match i.val with
  | 0 => NetHack.SokobanLinearPhases.Map11.heroesRegion16.filter fun c =>
      !(decide (c = 137 ∨ c = 191 ∨ c = 192 ∨ c = 193 ∨ c = 194 ∨ c = 216 ∨
        c = 217 ∨ c = 218 ∨ c = 219 ∨ c = 220))
  | 1 => U.filter fun c => !(decide (c = 138 ∨ c = 164))
  | 2 => U.filter fun c => !(decide (c = 164))
  | _ => U
def paid (source : Cell) (dir : Dir) : Prop :=
  (source = 137 ∧ dir = .west) ∨ (source = 138 ∧ (dir = .east ∨ dir = .west)) ∨
  (source = 191 ∧ dir = .east) ∨ (source = 216 ∧ dir = .east)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
end Owner1007.WestAfter11
