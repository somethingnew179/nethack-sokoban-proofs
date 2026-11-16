import Owner1007.CageFour12
namespace Owner1007.Post18712
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def upper : List Cell := [108,158,159,186,161]
def core (i : Fin 10) : List Cell := match i.val%4 with
 | 0 => [210,237,238,262]
 | 1 => [210,211,238,262]
 | 2 => [184,211,238,262]
 | _ => [184,211,238,236]
def locks (i : Fin 10) : List Cell :=
 if i.val<8 then upper++[212,if i.val<4 then 239 else 213]++core i
 else if i.val=8 then [210,236] else [184,210]
def region (i : Fin 10) : List Cell :=
 if h:i.val<4 then (Cage10.region ⟨i.val+4,by omega⟩).erase 239 ++ [187]
 else if h2:i.val<8 then Cage10.region ⟨i.val-4,by omega⟩
 else soko1_2.board.floor.filter fun c => !(locks i).contains c
def paid (source : Cell) (dir : Dir) : Prop :=
 source∈upper ∨ source=212 ∨ (source=239 ∧ dir≠.north) ∨ source=213 ∨
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
def paidSources : List Cell := upper ++ [212,239,213,237,211,210,184,238,262,236]
def gateEvent (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 ((source=186 ∧ dir=.west) ∨ (source=211 ∧ dir=.north)) ∧
 ([158,159,185,210]⊆185::(locks i).erase source ∨
  [158,159,184,185]⊆185::(locks i).erase source)
def quadEvent (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 source=212 ∧ dir=.west ∧ [210,211,237,262]⊆211::(locks i).erase source
def priceFour (source : Cell) (dir : Dir) : Prop :=
 ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧
 (4:Int)≤1+Generated.soko1_2Potential.boulder dest-Generated.soko1_2Potential.boulder source
def priceTwo (source : Cell) (dir : Dir) : Prop :=
 source∉([186,212] : List Cell) ∧ ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧
 (2:Int)≤1+Generated.soko1_2Potential.boulder dest-Generated.soko1_2Potential.boulder source
def classified (i : Fin 10) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (locks i) source dir ∨ gateEvent i source dir ∨
 quadEvent i source dir ∨ priceFour source dir ∨ priceTwo source dir
instance (i : Fin 10) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by
 unfold classified gateEvent quadEvent priceFour priceTwo
 infer_instance
def basic (i : Fin 8) : Fin 10 := ⟨i.val,by have h:=i.isLt; omega⟩
def classificationNode (i : Fin 8) : Bool :=
 (region (basic i)).all fun hero => allDirs.all fun dir => paidSources.all fun source =>
 decide (advance soko1_2.board hero dir=some source → paid source dir → classified (basic i) source dir)

theorem unique : ∀ i, (locks i).Nodup := by decide +kernel
theorem pairInside : ∀ i : Fin 10, i.val<8 → [186,212]⊆locks i := by decide +kernel
theorem badPair : ∀ i : Fin 10, 8≤i.val →
 [210,236]⊆locks i ∨ [184,210]⊆locks i := by decide +kernel
theorem paid_sources (source : Cell) (dir : Dir) (pays : paid source dir) : source∈paidSources := by
 rcases pays with h|h|h|h|h|h|h|h|h|h|h
 · exact List.mem_append_left _ h
 all_goals simp_all [paidSources,upper]
theorem source_pair_outside : ∀ source∈paidSources, source∉([186,212] : List Cell) →
 source∈VerticalPair12.region false 0 := by decide +kernel
end Owner1007.Post18712

