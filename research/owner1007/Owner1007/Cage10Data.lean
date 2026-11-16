import Owner1007.PricedCorral11
import NetHack.Sokoban.Generated.Soko12Potential
namespace Owner1007.Cage10
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def upper : List Cell := [108,158,159,186,187]
def locks : Fin 10 → List Cell
 | 0 => [108,158,159,186,187,210,213,237,238,262]
 | 1 => [108,158,159,186,187,210,213,211,238,262]
 | 2 => [108,158,159,186,187,184,213,211,238,262]
 | 3 => [108,158,159,186,187,184,213,211,238,236]
 | 4 => [108,158,159,186,187,210,212,237,238,262]
 | 5 => [108,158,159,186,187,210,212,211,238,262]
 | 6 => [108,158,159,186,187,184,212,211,238,262]
 | 7 => [108,158,159,186,187,184,212,211,238,236]
 | 8 => upper ++ [210,236]
 | 9 => upper ++ [184,210]
def region (i : Fin 10) : List Cell :=
 match i.val with
 | 0 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,239,241,242,244,245,246,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 1 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,236,237,239,241,242,244,245,246,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 2 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,210,214,215,216,218,219,220,236,237,239,241,242,244,245,246,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 3 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,214,215,216,218,219,220,237,239,241,242,244,245,246,262,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 4 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,239,241,242,244,245,246,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 5 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,236,237,239,241,242,244,245,246,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 6 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,210,213,214,215,216,218,219,220,236,237,239,241,242,244,245,246,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | 7 => [115,116,117,140,141,142,143,163,164,166,167,168,169,189,190,191,192,193,194,213,214,215,216,218,219,220,237,239,241,242,244,245,246,262,263,264,265,270,271,272,288,289,290,291,292,293,294,296,297,317,318,319,320,322,345,348,370,371,372,373,374,396,397,399,400]
 | _ => soko1_2.board.floor.filter fun c => !(locks i).contains c

def paid (source : Cell) (dir : Dir) : Prop :=
 source∈upper ∨ (source=213 ∧ dir≠.west) ∨ source=212 ∨
 (source=237 ∧ dir≠.north) ∨ source=211 ∨
 (source=210 ∧ dir≠.north) ∨ source=184 ∨ source=238 ∨
 (source=262 ∧ dir≠.north) ∨ (source=236 ∧ dir≠.north)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
def matrixNode (i : Fin 10) : Bool :=
 (region i).all fun hero => allDirs.all fun dir =>
  Corral11.walkCheck soko1_2.board locks region i hero dir &&
   (locks i).all fun source => decide (advance soko1_2.board hero dir ≠ some source ∨
     BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir ∨
     Corral11.Shift soko1_2.board soko1_2.initial.holes locks region i source dir)
def paidSources : List Cell := upper ++ [213,212,237,211,210,184,238,262,236]
def upperEvent (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 source=187 ∧ dir=.north ∧ [186,212]⊆locks i
def gateEvent (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 source=211 ∧ dir=.north ∧
 ([158,159,185,210]⊆185::(locks i).erase source ∨
  [158,159,184,185]⊆185::(locks i).erase source)
def squareEvent (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 ((source=211 ∧ dir=.east) ∨ (source=238 ∧ dir=.north)) ∧
 [186,187,212,213]⊆212::(locks i).erase source
def priceTwo (source : Cell) (dir : Dir) : Prop :=
 source∉upper ∧ ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧
 (2:Int)≤1+Generated.soko1_2Potential.boulder dest-Generated.soko1_2Potential.boulder source
def classified (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (locks i) source dir ∨ upperEvent i source dir ∨
 gateEvent i source dir ∨ squareEvent i source dir ∨ priceTwo source dir
instance (i : Fin 10) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by
 unfold classified upperEvent gateEvent squareEvent priceTwo
 infer_instance
def basic (i : Fin 8) : Fin 10 := ⟨i.val,by have h:=i.isLt; omega⟩
def classificationNode (i : Fin 8) : Bool :=
 (region (basic i)).all fun hero => allDirs.all fun dir => paidSources.all fun source =>
 decide (advance soko1_2.board hero dir=some source → paid source dir → classified (basic i) source dir)

theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem upperInside : ∀ i, upper⊆locks i := by decide +kernel
theorem upperGuard : ∀ i hero, hero∈region i → ∀ dir source, source∈upper →
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir := by
 intro i hero hi dir source member _
 exact Or.inr (Or.inl member)
theorem badPair : ∀ i : Fin 10, 8≤i.val →
 [210,236]⊆locks i ∨ [184,210]⊆locks i := by decide +kernel

theorem paid_sources (source : Cell) (dir : Dir) (pays : paid source dir) : source∈paidSources := by
 rcases pays with h|h|h|h|h|h|h|h|h|h
 · exact List.mem_append_left _ h
 all_goals simp_all [paidSources,upper]

theorem hard_targets :
 pushTargets soko1_2.board 187 .north=[161] ∧
 pushTargets soko1_2.board 211 .north=[185] ∧
 pushTargets soko1_2.board 211 .east=[212] ∧
 pushTargets soko1_2.board 238 .north=[212] := by decide +kernel
theorem hard_clear : ∀ c∈([161,185,212] : List Cell), c∉soko1_2.initial.holes := by decide +kernel
theorem locked210 : Locked soko1_2.board [210,236] := locked_of_check _ _ (by decide +kernel)
theorem locked184 : Locked soko1_2.board [184,210] := locked_of_check _ _ (by decide +kernel)
theorem lockedUpperSquare : Locked soko1_2.board [158,159,184,185] := locked_of_check _ _ (by decide +kernel)
theorem debt210 : debtOf Generated.soko1_2Potential [210,236]=15 := by decide +kernel
theorem debt184 : debtOf Generated.soko1_2Potential [184,210]=17 := by decide +kernel

end Owner1007.Cage10

