import Owner1007.FastCorral11
import Owner1007.ZeroWord11
namespace Owner1007.CentralFirst11
open NetHack.Sokoban
def sources : List Cell := [266,268,293]
def locks (_ : Fin 1) : List Cell := sources
def region (_ : Fin 1) : List Cell := [27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,53,54,55,56,57,58,59,76,85,102,106,107,108,109,110,111,112,113,114,115,116,128,132,133,134,135,136,137,138,139,140,141,142,154,164,180,183,184,185,186,187,188,189,190,191,192,193,194,206,209,210,211,212,213,214,215,216,217,218,219,220,232,239,258,262,263,264,265,269,270,271,284,288,289,290,291,292,294,295,296,297,310,314,315,316,317,318,319,320,321,322,336,345,362,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
def paid (source : Cell) (_ : Dir) : Prop := source∈sources
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
def positive (source : Cell) (dir : Dir) : Prop :=
 ((source=266∨source=268) ∧dir=.east) ∨ (source=293 ∧(dir=.east∨dir=.south))
instance (source : Cell) (dir : Dir) : Decidable (positive source dir) := by unfold positive;infer_instance
def Shape (source : Cell) (dir : Dir) : Prop :=
 positive source dir ∨ (source=293 ∧dir=.west) ∨ (source=268∧dir=.west) ∨ (source=293∧dir=.north)
instance (source : Cell) (dir : Dir) : Decidable (Shape source dir) := by unfold Shape;infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 0
end Owner1007.CentralFirst11
