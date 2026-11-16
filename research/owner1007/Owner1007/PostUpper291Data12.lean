import Owner1007.RingUpperBound12
import Owner1007.Post187Seven12
namespace Owner1007.PostUpper29112
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def locks (_ : Fin 1) : List Cell := [108,158,159,186,161,212,291,210,237,238,263,290]
def region (_ : Fin 1) : List Cell :=
 [115,116,117,140,141,142,143,163,164,166,167,168,169,187,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,264,265,270,271,272,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
def paid (source : Cell) (_ : Dir) : Prop := source∈locks 0
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
theorem matrix : PricedCorral11.checkExcept soko1_2.board soko1_2.initial.holes locks region paid=true := by decide +kernel
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
def classified (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (locks 0) source dir ∨
 (source=186 ∧ dir=.west) ∨ (source=161 ∧ dir=.north) ∨
 (source=212 ∧ dir=.west) ∨ (source=263 ∧ dir=.west) ∨
 (source=291 ∧ dir=.north) ∨ (source=291 ∧ dir=.south)
instance (source : Cell) (dir : Dir) : Decidable (classified source dir) := by unfold classified; infer_instance
theorem classification : ∀ hero∈region 0, ∀ dir∈allDirs, ∀ source∈locks 0,
 advance soko1_2.board hero dir=some source → classified source dir := by decide +kernel
theorem gate : [158,159,185,210]⊆185::(locks 0).erase 186 := by decide +kernel
theorem quad : Quad29012.locks 0⊆211::(locks 0).erase 212 := by decide +kernel
theorem seven : Post187Seven12.locks 0⊆262::(locks 0).erase 263 := by decide +kernel
theorem reset : RingUpper12.locks 0⊆265::(locks 0).erase 291 := by decide +kernel
#print axioms matrix
#print axioms classification
end Owner1007.PostUpper29112
