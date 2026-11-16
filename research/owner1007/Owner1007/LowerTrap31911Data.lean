import Owner1007.FastCorral11
import Owner1007.ZeroWord11
namespace Owner1007.LowerTrap31911
open NetHack.Sokoban
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def H := NetHack.SokobanLinearPhases.Map11.heroesRegion16
def locks (_ : Fin 1) : List Cell := [266,268,293,319,321]
def region (_ : Fin 1) : List Cell := [27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,53,54,55,56,57,58,59,76,85,102,106,107,108,109,110,111,112,113,114,115,116,128,132,133,134,135,136,137,138,139,140,141,142,154,164,180,183,184,185,186,187,188,189,190,191,192,193,194,206,209,210,211,212,213,214,215,216,217,218,219,220,232,239,258,262,263,264,265,284,288,289,290,291,292,310,314,315,316,317,318,336,362]
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=266∨source=293∨source=319) ∧dir=.east
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
def sources : List Cell := [266,293,319]
theorem paid_source (source : Cell) (dir : Dir) (pays : paid source dir) : source∈sources := by
 rcases pays with ⟨pays,_⟩
 rcases pays with rfl|rfl|rfl <;> decide
theorem unique (i : Fin 1) : (locks i).Nodup := by change ([266,268,293,319,321] : List Cell).Nodup;decide
theorem size (i : Fin 1) : (locks i).length=5 := rfl
theorem floor (i : Fin 1) : region i⊆soko1_1.board.floor := by
 have all : (region 0).all (fun c=>decide (c∈soko1_1.board.floor))=true := by decide +kernel
 intro c member
 exact of_decide_eq_true (List.all_eq_true.mp all c member)

end Owner1007.LowerTrap31911
