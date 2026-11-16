import Owner1007.RingPrepared12
import Owner1007.TwoReserves12
namespace Owner1007.After29012
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def locks : Fin 4 → List Cell
 | 0 => [108,158,159,186,187,213,265,210,237,238,263,289]
 | 1 => [108,158,159,186,187,212,265,210,237,238,263,289]
 | 2 => [108,158,159,186,187,213,239,210,237,238,263,289]
 | 3 => [108,158,159,186,187,212,239,210,237,238,263,289]
def region : Fin 4 → List Cell
 | 0 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,241,242,244,245,246,264,270,271,272,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 1 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,264,270,271,272,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 2 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,241,242,244,245,246,264,265,270,271,272,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 3 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,241,242,244,245,246,264,265,270,271,272,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
def paid (source : Cell) (dir : Dir) : Prop :=
 (source=263 ∧ dir=.west) ∨ (source=289 ∧ dir=.west) ∨ source∈CageLedger12.Upper ∨
 (source=213 ∧ dir≠.west) ∨ source=212 ∨ source=239 ∨ (source=265 ∧ dir=.south) ∨ (source=238 ∧ dir=.north)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
def sources : List Cell := CageLedger12.Upper++[263,289,213,212,239,265,238]
def matrixNode (i : Fin 4) : Bool :=
 (region i).all fun hero => allDirs.all fun dir =>
  Corral11.walkCheck soko1_2.board locks region i hero dir &&
   (locks i).all fun source => decide (advance soko1_2.board hero dir ≠ some source ∨
     BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir ∨
     Corral11.Shift soko1_2.board soko1_2.initial.holes locks region i source dir)
def squareDest (source : Cell) : Cell := if source=239 then 213 else 212
def square (i : Fin 4) (source : Cell) (dir : Dir) : Prop :=
 ((source=239 ∧ dir=.north) ∨ (source=238 ∧ dir=.north)) ∧
 [186,187,212,213]⊆squareDest source::(locks i).erase source
def foreignTwo (source : Cell) (dir : Dir) : Prop :=
 source∉CageLedger12.Upper ∧ source∉RingAfter12.locks true 0 ∧
 ∀ dest∈pushTargets soko1_2.board source dir, dest∉soko1_2.initial.holes ∧
 (2:Int)≤1+Generated.soko1_2Potential.boulder dest-Generated.soko1_2Potential.boulder source
def highFour (source : Cell) (dir : Dir) : Prop :=
 source∉CageLedger12.Upper ∧
 ∀ dest∈pushTargets soko1_2.board source dir, dest∉soko1_2.initial.holes ∧
 (4:Int)≤1+Generated.soko1_2Potential.boulder dest-Generated.soko1_2Potential.boulder source
def classified (i : Fin 4) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (locks i) source dir ∨ (source=263 ∧ dir=.west) ∨
 (source=187 ∧ dir=.north ∧ [186,212]⊆locks i) ∨ square i source dir ∨ foreignTwo source dir ∨ highFour source dir
instance (i : Fin 4) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by
 unfold classified square squareDest foreignTwo highFour
 infer_instance
def classificationNode (i : Fin 4) : Bool :=
 (region i).all fun hero => allDirs.all fun dir => sources.all fun source =>
 decide (advance soko1_2.board hero dir=some source → paid source dir → classified i source dir)
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem upperInside : ∀ i, CageLedger12.Upper⊆locks i := by decide +kernel
theorem ringInside : ∀ i, RingAfter12.locks true 0⊆locks i := by decide +kernel
def cageIndex (i : Fin 4) : Fin 10 := if i.val%2=0 then 0 else 4
theorem cage_activation : ∀ i, Cage10.locks (cageIndex i)⊆262::(locks i).erase 263 := by decide +kernel
theorem cage_hero : ∀ i, (263:Cell)∈Cage10.region (cageIndex i) := by decide +kernel
theorem upper_after187 : ∀ i, [186,212]⊆locks i → [186,212]⊆161::(locks i).erase 187 := by decide +kernel
theorem ring_after187 : ∀ i, RingAfter12.locks true 0⊆161::(locks i).erase 187 := by decide +kernel
theorem sources_paid (source : Cell) (dir : Dir) (h : paid source dir) : source∈sources := by
 rcases h with h|h|h|h|h|h|h|h
 · simp_all [sources,CageLedger12.Upper]
 · simp_all [sources,CageLedger12.Upper]
 · exact List.mem_append_left _ h
 all_goals simp_all [sources,CageLedger12.Upper]
theorem upper_bonus : ∀ source∈sources, source∉CageLedger12.Upper →
 RightEnergy12.cert.bonus source (NetHack.Sokoban.PatternCorrection.project CageLedger12.Upper)=2 := by decide +kernel
theorem ring_hero : ∀ source∈sources, source∉CageLedger12.Upper → source∉RingAfter12.locks true 0 →
 source∈TwoReserves12.region true := by decide +kernel
end Owner1007.After29012

