import Owner1007.FastCorral11
import Owner1007.ZeroWord11
namespace Owner1007.Triangle29111
open NetHack.Sokoban
def H := NetHack.SokobanLinearPhases.Map11.heroesRegion16
def locks (_ : Fin 1) : List Cell := [264,266,291]
def region (_ : Fin 1) : List Cell := H.filter fun c => c<262 || 12≤c%26 || c=265
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=264 ∧ dir=.west) ∨(source=266 ∧dir=.east) ∨(source=291∧dir=.south)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
def sources : List Cell := [264,266,291]
def threshold (source : Cell) : Int := if source=291 then 20 else 2

end Owner1007.Triangle29111
