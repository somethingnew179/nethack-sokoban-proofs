import Owner1007.PreCageFacts12
import Owner1007.TokenPersistence
namespace Owner1007.RingTagFacts12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition
open Owner1007 Owner1007.PreCage12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem ring_tags_inside : ∀ i, ringS i∈ringLocks i ∧ ringTag i∈ringLocks i := by decide +kernel
theorem ring_tags_distinct : ∀ i, ringS i≠ringTag i := by decide +kernel

theorem ring_tag_update (i : Fin 4) (source : Cell) (dir : Dir) (j : Fin 4) (dest : Cell)
 (allowed : ringAllowed i source dir j dest) :
 update [ringS i] (.push source (.stay dest))=[ringS j] ∧
 update [ringTag i] (.push source (.stay dest))=[ringTag j] := by
 rcases allowed with h | h
 · obtain ⟨s,rfl,rfl,next,rfl⟩:=h
   have table : ∀ i j : Fin 4, ringS i=213 → j.val=i.val+1 →
    update [ringS i] (.push 213 (.stay 212))=[ringS j] ∧
    update [ringTag i] (.push 213 (.stay 212))=[ringTag j] := by decide +kernel
   exact table i j s next
 · obtain ⟨t,rfl,rfl,next,rfl⟩:=h
   have table : ∀ i j : Fin 4, ringTag i=265 → j.val=i.val+2 →
    update [ringS i] (.push 265 (.stay 239))=[ringS j] ∧
    update [ringTag i] (.push 265 (.stay 239))=[ringTag j] := by decide +kernel
   exact table i j t next

def ringFixed : List Cell := U ++ [210,237,238,263,290]
theorem ring_fixed_inside : ∀ i, ringFixed⊆ringLocks i := by decide +kernel
theorem ring_fixed_guard_check : ∀ i, ∀ hero∈ringRegion i, ∀ dir∈allDirs, ∀ source∈ringFixed,
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (ringLocks i) source dir ∨ ringPaid source dir := by decide +kernel
theorem ring_fixed_guard : ∀ i hero, hero∈ringRegion i → ∀ dir source, source∈ringFixed →
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (ringLocks i) source dir ∨ ringPaid source dir := by
 intro i hero inside dir source member adjacent
 exact ring_fixed_guard_check i hero inside dir (Geometry.all_directions dir) source member adjacent
#print axioms ring_tag_update
#print axioms ring_fixed_guard
end Owner1007.RingTagFacts12

