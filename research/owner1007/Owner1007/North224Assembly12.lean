import Owner1007.NorthRingActivation12
import Owner1007.NorthLeftBudget12
import Owner1007.CheapNorth12
namespace Owner1007.North224Assembly12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.OwnedEvents12
abbrev p := Generated.soko1_2Potential

/-- The single continuation property required by this conditional assembly. -/
def RingReserve : Prop :=
 ∀ {state final dirs pushes moves outcomes history past pastMoves},
 Logged soko1_2.board state dirs final pushes moves outcomes →
 Trace soko1_2.board soko1_2.initial history state past pastMoves →
 ∀ group : List Cell, group.Nodup → group⊆state.boulders → Goal final →
 ∀ i : Fin 4, state.player∈PreCage12.ringRegion i → PreCage12.ringLocks i⊆group →
 6≤energy p group outcomes

theorem north_bound (reserve : RingReserve) {dirs final pushes moves}
 (trace : Trace soko1_2.board FirstSplit12.afterN dirs final pushes moves) (completed : Goal final) :
 224≤1+pushes := by
 by_cases enough : 224≤1+pushes
 · exact enough
 · have cheap : 1+pushes≤223 := by omega
   obtain ⟨outcomes,logged⟩ := log_exists trace (by decide +kernel)
   obtain ⟨beforeDirs,beforePushes,beforeMoves,before,middle,t,after,afterDirs,afterPushes,afterMoves,
       i,shape,first,checked,effect,last,hero,locks,sAt,tAt,current,unchanged⟩ :=
     NorthForcedRing12.forced_ring logged completed cheap
   have upper := NorthLeftBudget12.left_seven logged completed cheap
   change energy p NorthTagFacts12.selected outcomes≤7 at upper
   have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
   have selectedUnique : NorthTagFacts12.selected.Nodup := by decide +kernel
   have selectedSubset : NorthTagFacts12.selected⊆FirstSplit12.afterN.boulders := by decide +kernel
   have old := first.end_subset initialUnique NorthTagFacts12.selected selectedUnique selectedSubset
   have reached := NorthBound12.north_reached.append first.trace
   have actualUnique := reached.boulders_nodup (by decide +kernel)
   have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
   have nextUnique := GhostSubset.update_unique _ _ _ effect nextActual _ old.1 old.2
   have nextSubset := GhostSubset.update_subset _ _ _ effect _ old.1 old.2
   have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
   obtain ⟨j,ringHero,ringInside⟩ := NorthRingActivation12.activation effect i current locks
   have future := reserve last nextReached _ nextUnique nextSubset completed j ringHero ringInside
   have owner : (291 : Cell)∈endGroup NorthTagFacts12.selected before :=
     locks (NorthRingActivation12.source_member i current)
   have prefixNN := first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthTagFacts12.selected
   change 0≤ownSlack p NorthTagFacts12.selected before at prefixNN
   have price : slack p (.push 291 (.stay 290))=2 := by decide +kernel
   rw [shape,energy_at_split] at upper
   simp only [NetHack.Sokoban.GhostProjection.projectedOutcome,if_pos owner,price] at upper
   omega

/-- Still conditional on RingReserve; no universal224 claim until its checked instantiation. -/
theorem canonical_bound (reserve : RingReserve) {dirs final pushes moves}
 (trace : Trace soko1_2.board soko1_2.initial dirs final pushes moves) (completed : Goal final) :
 224≤pushes := by
 by_cases large : 224≤pushes
 · exact large
 · obtain ⟨q,m,ds,count,north⟩ := CheapNorth12.all_cheap_completions_start_north trace completed (by omega)
   have bound := north_bound reserve north completed
   omega
#print axioms north_bound
#print axioms canonical_bound
end Owner1007.North224Assembly12
