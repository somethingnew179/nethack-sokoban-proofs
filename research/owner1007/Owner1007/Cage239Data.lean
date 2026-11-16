import Owner1007.CageFour12
import Owner1007.Quad211Trap12
namespace Owner1007.Cage23912
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def locks (i : Fin 10) : List Cell := Cage10.locks i ++ [239]
def region (i : Fin 10) : List Cell := (Cage10.region i).erase 239
def paid (source : Cell) (dir : Dir) : Prop := Cage10.paid source dir ∨ source=239
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid; infer_instance
def matrixNode (i : Fin 10) : Bool :=
 (region i).all fun hero => allDirs.all fun dir =>
  Corral11.walkCheck soko1_2.board locks region i hero dir &&
   (locks i).all fun source => decide (advance soko1_2.board hero dir ≠ some source ∨
     BlockedPush soko1_2.board (locks i) source dir ∨ paid source dir ∨
     Corral11.Shift soko1_2.board soko1_2.initial.holes locks region i source dir)
def paidSources : List Cell := Cage10.paidSources ++ [239]
def upperEvent (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 source=187 ∧ dir=.north ∧ 4≤i.val ∧ i.val<8
def gateEvent (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 source=211 ∧ dir=.north ∧
 ([158,159,185,210]⊆185::(locks i).erase source ∨
  [158,159,184,185]⊆185::(locks i).erase source)
def squareDest (source : Cell) : Cell := if source=239 then 213 else 212
def squareEvent (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 ((source=211 ∧ dir=.east) ∨ (source=238 ∧ dir=.north) ∨ (source=239 ∧ dir=.north)) ∧
 [186,187,212,213]⊆squareDest source::(locks i).erase source
def quadEvent (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 source=212 ∧ dir=.west ∧ [210,211,237,262]⊆211::(locks i).erase source
def escapeEvent (source : Cell) (dir : Dir) : Prop := source=239 ∧ dir=.south
def priceSix (source : Cell) (dir : Dir) : Prop :=
 ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧
 (6:Int)≤1+Generated.soko1_2Potential.boulder dest-Generated.soko1_2Potential.boulder source
def classified (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (locks i) source dir ∨ upperEvent i source dir ∨
 gateEvent i source dir ∨ squareEvent i source dir ∨ quadEvent i source dir ∨
 escapeEvent source dir ∨ priceSix source dir
instance (i : Fin 10) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by
 unfold classified upperEvent gateEvent squareEvent quadEvent escapeEvent priceSix squareDest
 infer_instance
def basic (i : Fin 8) : Fin 10 := ⟨i.val,by have h:=i.isLt; omega⟩
def classificationNode (i : Fin 8) : Bool :=
 (region (basic i)).all fun hero => allDirs.all fun dir => paidSources.all fun source =>
 decide (advance soko1_2.board hero dir=some source → paid source dir → classified (basic i) source dir)
theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem badPair : ∀ i : Fin 10, 8≤i.val →
 [210,236]⊆locks i ∨ [184,210]⊆locks i := by decide +kernel
theorem paid_sources (source : Cell) (dir : Dir) (pays : paid source dir) : source∈paidSources := by
 rcases pays with old | rfl
 · exact List.mem_append_left _ (Cage10.paid_sources source dir old)
 · exact List.mem_append_right _ (by simp)
end Owner1007.Cage23912

