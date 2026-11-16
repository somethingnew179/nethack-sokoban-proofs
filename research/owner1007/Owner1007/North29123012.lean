import Owner1007.NorthMain22912
import Owner1007.NorthParityPrice12
namespace Owner1007.North29123012
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting Owner1007.OwnedEvents12 Owner1007.North22812
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The actual291West main-event branch requires230, using the owned
Ring11 reserve and consumed-Left parity. No global optimality claim follows. -/
theorem first291_west {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final)
 {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
 (shape : outcomes=before++.push 291 (.stay 290)::after)
 (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .west=some t)
 (effect : Matches middle t (.push 291 (.stay 290)))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (i : Fin 10) (hero : middle.player∈PreCage12.northRegion i)
 (locks : PreCage12.northLocks i⊆endGroup L before)
 (sourceMember : (291:Cell)∈PreCage12.northLocks i) : 230≤1+pushes := by
 have current : PreCage12.northTag i=291 := by
   have all : ∀ i,291∈PreCage12.northLocks i→PreCage12.northTag i=291 := by decide +kernel
   exact all i sourceMember
 have reached := NorthBound12.north_reached.append first.trace
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have oldGroup := first.end_subset (by decide +kernel) L (by decide +kernel) (by decide +kernel)
 have ownerL : (291:Cell)∈endGroup L before := locks sourceMember
 have nextActual := step_boulders_nodup _ _ _ _ actualUnique checked
 have nextUnique := GhostSubset.update_unique middle t (.push 291 (.stay 290)) effect nextActual
   (endGroup L before) oldGroup.1 oldGroup.2
 have nextSubset := GhostSubset.update_subset middle t (.push 291 (.stay 290)) effect
   (endGroup L before) oldGroup.1 oldGroup.2
 obtain ⟨shift,newHero⟩ := ring_activation i current
 have kept := CageFour12.shifted_inside (PreCage12.north_unique i) locks ownerL shift
 have nextHero : t.state.player∈PreCage12.ringRegion (ringIndex i) := by
   rw [matches_hero middle t (.push 291 (.stay 290)) effect]
   exact newHero
 have nextReached := reached.append (Trace.cons checked (Trace.nil t.state))
 have later := RingEleven12.ring_energy_eleven last nextReached
   (update (endGroup L before) (.push 291 (.stay 290))) nextUnique nextSubset completed nextHero kept
 change 11≤energy p (update (endGroup L before) (.push 291 (.stay 290))) after at later
 have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid L
 change 0≤ownSlack p L before at nn
 have one : slack p (.push 291 (.stay 290))=2 := by decide +kernel
 have lower : 13≤energy p L outcomes := by
   rw [shape,energy_at_split]
   simp only [projectedOutcome,if_pos ownerL,one]
   omega
 change 13≤energy p NorthPriceBalance12.Left outcomes at lower
 exact NorthParityPrice12.thirteen_implies_230 logged completed lower
#print axioms first291_west
end Owner1007.North29123012
