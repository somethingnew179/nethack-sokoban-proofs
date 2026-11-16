import Owner1007.PreCageFacts12
import NetHack.Sokoban.Generated.Soko12Potential
namespace Owner1007.PreRingHeads12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open Owner1007 Owner1007.PreCage12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def sources : List Cell := U++[210,237,263,290,213,212,239,265,238]
def extraTwo (source : Cell) (dir : Dir) : Prop :=
 source∉U ∧ ¬RingCut12.paid source dir ∧ ∀ dest∈pushTargets soko1_2.board source dir,
 dest∉soko1_2.initial.holes ∧
 (2:Int)≤1+Generated.soko1_2Potential.boulder dest-Generated.soko1_2Potential.boulder source
def square (i : Fin 4) (source : Cell) (dir : Dir) : Prop :=
 (source=239 ∧ dir=.north ∧ [186,187,212,213]⊆213::(ringLocks i).erase source) ∨
 (source=238 ∧ dir=.north ∧ [186,187,212,213]⊆212::(ringLocks i).erase source)
def classified (i : Fin 4) (source : Cell) (dir : Dir) : Prop :=
 BlockedPush soko1_2.board (ringLocks i) source dir ∨
 RingCut12.paid source dir ∨
 (source=187 ∧ dir=.north ∧ ringS i=212) ∨
 square i source dir ∨ extraTwo source dir
instance (i : Fin 4) (source : Cell) (dir : Dir) : Decidable (classified i source dir) := by
 unfold classified square extraTwo
 infer_instance
def node (i : Fin 4) : Bool :=
 (ringRegion i).all fun hero => allDirs.all fun dir => sources.all fun source =>
 decide (advance soko1_2.board hero dir=some source → ringPaid source dir → classified i source dir)
theorem checked0 : node 0=true := by decide +kernel
theorem checked1 : node 1=true := by decide +kernel
theorem checked2 : node 2=true := by decide +kernel
theorem checked3 : node 3=true := by decide +kernel
theorem checked (i : Fin 4) : node i=true := by
 obtain ⟨v,bound⟩:=i
 have choices : v=0∨v=1∨v=2∨v=3 := by omega
 rcases choices with rfl|rfl|rfl|rfl
 · exact checked0
 · exact checked1
 · exact checked2
 · exact checked3
theorem classification (i : Fin 4) (hero : Cell) (inside : hero∈ringRegion i)
 (dir : Dir) (source : Cell) (member : source∈sources)
 (adjacent : advance soko1_2.board hero dir=some source) (paid : ringPaid source dir) :
 classified i source dir := by
 have row := List.all_eq_true.mp
  (List.all_eq_true.mp (List.all_eq_true.mp (checked i) hero inside)
   dir (Geometry.all_directions dir)) source member
 exact of_decide_eq_true row adjacent paid
theorem source_cases (source : Cell) (dir : Dir) (pays : ringPaid source dir) : source∈sources := by
 rcases pays with r|u|s|h|h|h
 · rcases r with h|h|h|h <;> simp_all [sources,U]
 · exact List.mem_append_left _ u
 · rcases s with h|h <;> simp_all [sources,U]
 all_goals simp_all [sources,U]
theorem ring_region_inside : ∀ i, ringRegion i⊆RingCut12.region 0 := by decide +kernel
theorem upper_pair : ∀ i, ringS i=212 → [186,212]⊆ringLocks i := by decide +kernel
theorem square_targets :
 pushTargets soko1_2.board 239 .north=[213] ∧ pushTargets soko1_2.board 238 .north=[212] := by decide +kernel
#print axioms classification
#print axioms source_cases
end Owner1007.PreRingHeads12

