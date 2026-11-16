import Owner1007.FastCorral11
import Owner1007.ZeroWord11
namespace Owner1007.Gate265Transport11
open NetHack.Sokoban
def lower : List Cell := [262,263,264,266,267,268,269,270,271,288,289,290,291,292,293,294,295,296,297,314,315,316,317,318,319,320,321,322,345,365,366,367,368,369,370,371,372,391,392,393,394,395,396,397,398,417,418,419]
def upper : List Cell := [27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,53,54,55,56,57,58,59,76,85,102,106,107,108,109,110,111,112,113,114,115,116,128,132,133,134,135,136,137,138,139,140,141,142,154,164,180,183,184,185,186,187,188,189,190,191,192,193,194,206,209,210,211,212,213,214,215,216,217,218,219,220,232,239,258,278,279,280,281,282,284,302,304,305,306,307,308,310,330,331,332,333,334,336,354,356,357,358,359,360,362,382,383,384,385,386,406,408,409,410,411,412,434,435,436,437,438]
def lowerOrigins : List Cell := [264,266,268,293,315,317,321,367]
def upperOrigins : List Cell := [133,135,137,139,141,186,188,191,193,212]
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=239∧dir=.south) ∨(source=264∧dir=.east) ∨(source=266∧dir=.west) ∨(source=291∧dir=.north)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
def directionCheck (region : List Cell) (dir : Dir) : Bool :=
 region.all fun source=>if paid source dir then true else
   (pushTargets soko1_1.board source dir).all (fun dest=>decide (dest∈region))
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem lower_initial : lowerOrigins⊆lower := by decide +kernel
theorem upper_initial : upperOrigins⊆upper := by decide +kernel
theorem original_partition : (upperOrigins++lowerOrigins).Perm soko1_1.initial.boulders := by decide +kernel
theorem lower_noholes : lower.all (fun c=>decide (c∉soko1_1.initial.holes))=true := by decide +kernel
end Owner1007.Gate265Transport11
