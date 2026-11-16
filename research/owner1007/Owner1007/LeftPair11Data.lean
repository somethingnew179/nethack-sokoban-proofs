import Owner1007.FastCorral11
import Owner1007.ZeroWord11
namespace Owner1007.LeftPair11
open NetHack.Sokoban
def H : List Cell := NetHack.SokobanLinearPhases.Map11.heroesRegion16
def cut0Locks (_ : Fin 1) : List Cell := [186,212]
def cut0Region (_ : Fin 1) : List Cell := H.filter fun c =>
  !(decide (c=183 ∨ c=184 ∨ c=185 ∨ c=186 ∨ c=209 ∨ c=210 ∨ c=211 ∨ c=212))
def cut0Paid (source : Cell) (dir : Dir) : Prop := (source=186 ∨ source=212) ∧ dir=.west
instance (source : Cell) (dir : Dir) : Decidable (cut0Paid source dir) := by unfold cut0Paid; infer_instance
def locks (i : Fin 2) : List Cell := if i.val=0 then [185,212] else [186,211]
def region (i : Fin 2) : List Cell := H.filter fun c =>
  !(decide (c=183 ∨ c=184 ∨ c=185 ∨ c=209 ∨ c=210 ∨ c=211 ∨
    (i.val=0 ∧ c=212) ∨ (i.val=1 ∧ c=186)))
def paid (source : Cell) (dir : Dir) : Prop :=
  (source=185 ∨ source=186 ∨ source=211 ∨ source=212) ∧ dir=.west
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
end Owner1007.LeftPair11
