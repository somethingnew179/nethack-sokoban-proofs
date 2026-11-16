import Owner1007.Post187Seven12
import Owner1007.Quad289Bound12
import Owner1007.TwoReserves12
import Owner1007.RingPrepared12
namespace Owner1007.FarUpper12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def upper : List Cell := [108,158,159,186,161]
def locks : Fin 3 → List Cell
 | 0 => [108,158,159,186,161,212,265,210,237,238,263,289]
 | 1 => [108,158,159,186,161,212,239,210,237,238,263,289]
 | 2 => [108,158,159,186,161,212,213,210,237,238,263,289]
def region : Fin 3 → List Cell
 | 0 => [115,116,117,140,141,142,143,163,164,166,167,168,169,187,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,264,270,271,272,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 1 => [115,116,117,140,141,142,143,163,164,166,167,168,169,187,189,190,191,192,193,194,213,214,215,216,218,219,220,241,242,244,245,246,264,265,270,271,272,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 2 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,239,241,242,244,245,246,264,265,270,271,272,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
def paid (source : Cell) (dir : Dir) : Prop :=
 source∈upper ∨ source=212 ∨ (source=265 ∧ dir≠.north) ∨
 (source=239 ∧ dir≠.north) ∨ source=213 ∨ (source=263 ∧ dir=.west) ∨ (source=289 ∧ dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
def sources : List Cell := upper++[212,265,239,213,263,289]
def matrixNode (i : Fin 3) : Bool :=
 (region i).all fun hero => allDirs.all fun dir =>
  Corral11.walkCheck soko1_2.board locks region i hero dir &&
   (locks i).all fun source => decide (advance soko1_2.board hero dir ≠ some source ∨
     BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir ∨
     Corral11.Shift soko1_2.board soko1_2.initial.holes locks region i source dir)
def gate (i : Fin 3) (source : Cell) (dir : Dir) : Prop :=
 source=186 ∧ dir=.west ∧ [158,159,185,210]⊆185::(locks i).erase source
def quad (i : Fin 3) (source : Cell) (dir : Dir) : Prop :=
 source=212 ∧ dir=.west ∧ [210,211,237,263,289]⊆211::(locks i).erase source
def foreignTwo (source : Cell) (dir : Dir) : Prop :=
 source∉([186,212]:List Cell) ∧ source∉RingAfter12.locks true 0 ∧
 ∀ dest∈pushTargets soko1_2.board source dir, dest∉soko1_2.initial.holes ∧
 (2:Int)≤1+Generated.soko1_2Potential.boulder dest-Generated.soko1_2Potential.boulder source
def priceSix (source : Cell) (dir : Dir) : Prop :=
 ∀ dest∈pushTargets soko1_2.board source dir, dest∉soko1_2.initial.holes ∧
 (6:Int)≤1+Generated.soko1_2Potential.boulder dest-Generated.soko1_2Potential.boulder source
def classified (i : Fin 3) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (locks i) source dir ∨ gate i source dir ∨ quad i source dir ∨
 (source=263 ∧ dir=.west) ∨ (source=289 ∧ dir=.west) ∨
 foreignTwo source dir ∨ priceSix source dir
instance (i : Fin 3) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by
 unfold classified gate quad foreignTwo priceSix
 infer_instance
def classificationNode (i : Fin 3) : Bool :=
 (region i).all fun hero => allDirs.all fun dir => sources.all fun source =>
 decide (advance soko1_2.board hero dir=some source → paid source dir → classified i source dir)
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem pairInside : ∀ i, ([186,212]:List Cell)⊆locks i := by decide +kernel
theorem ringInside : ∀ i, RingAfter12.locks true 0⊆locks i := by decide +kernel
theorem cage_activation : ∀ i, Post187Seven12.locks 0⊆262::(locks i).erase 263 := by decide +kernel
theorem cage_hero : (263:Cell)∈Post187Seven12.region 0 := by decide +kernel
theorem cage_credit : Post187Seven12.credit 0=7 := by decide +kernel
theorem pair_after289 : ∀ i, ([186,212]:List Cell)⊆288::(locks i).erase 289 := by decide +kernel
theorem sources_paid (source : Cell) (dir : Dir) (h : paid source dir) : source∈sources := by
 rcases h with h|h|h|h|h|h|h
 · exact List.mem_append_left _ h
 all_goals simp_all [sources,upper]
theorem foreign_ring_hero : ∀ source∈sources, source∉([186,212]:List Cell) → source∉RingAfter12.locks true 0 →
 source∈TwoReserves12.region true := by decide +kernel
theorem foreign_pair_hero : ∀ source∈sources, source∉([186,212]:List Cell) → source∉RingAfter12.locks true 0 →
 source∈VerticalPair12.region false 0 := by decide +kernel
end Owner1007.FarUpper12


