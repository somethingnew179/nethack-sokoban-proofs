import Owner1007.FastCorral11
import Owner1007.ZeroWord11
namespace Owner1007.PostCuts11
open NetHack.Sokoban
def H : List Cell := NetHack.SokobanLinearPhases.Map11.heroesRegion16
def without (cells blocked : List Cell) : List Cell := cells.filter fun c => !blocked.contains c
def rightLocks (_ : Fin 1) : List Cell := [191,217]
def rightRegion (_ : Fin 1) : List Cell := without H [191,192,193,194,217,218,219,220]
def rightPaid (source : Cell) (dir : Dir) : Prop := (source = 191 ∨ source = 217) ∧ dir = .east
instance (source : Cell) (dir : Dir) : Decidable (rightPaid source dir) := by unfold rightPaid; infer_instance
def entryLocks (_ : Fin 1) : List Cell := [113,139]
def entryRegion (_ : Fin 1) : List Cell := without H [113,114,115,116,139,140,141,142]
def entryPaid (source : Cell) (dir : Dir) : Prop := (source = 113 ∨ source = 139) ∧ dir = .east
instance (source : Cell) (dir : Dir) : Decidable (entryPaid source dir) := by unfold entryPaid; infer_instance
end Owner1007.PostCuts11
