import Owner1007.S211SidecarCut12
import Owner1007.NorthJTightCash12
namespace Owner1007.North238SidecarImpossible12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.SidecarCoreQuiet12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem impossible
 {final dirs pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤228)
 {d0 p0 m0 before middle t after d1 p1 m1}
 (shape : outcomes=before++.push 238 (.stay 264)::after)
 (first : Logged soko1_2.board FirstSplit12.afterN d0 middle p0 m0 before)
 (head : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (.push 238 (.stay 264)))
 (last : Logged soko1_2.board t.state d1 final p1 m1 after)
 (j : Fin 5) (oldLocks : NorthEvents12.locks j⊆endGroup NorthBound12.G before)
 (sGlobal : endGroup [213] before=[211])
 (cut : AfterJSharpCash12.SidecarCut t.state
   (update (endGroup NorthBound12.G before) (.push 238 (.stay 264))) final after) : False := by
 have initialUnique : FirstSplit12.afterN.boulders.Nodup := by decide +kernel
 have reached := NorthBound12.north_reached.append first.trace
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have facts := first.end_subset initialUnique NorthBound12.G (by decide +kernel) (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ actualUnique head
 have nextUnique := GhostSubset.update_unique middle t (.push 238 (.stay 264)) effect nextActual
   (endGroup NorthBound12.G before) facts.1 facts.2
 have nextSubset := GhostSubset.update_subset middle t (.push 238 (.stay 264)) effect
   (endGroup NorthBound12.G before) facts.1 facts.2
 have nextReached := reached.append (Trace.cons head (Trace.nil t.state))
 have owner : (238:Cell)∈endGroup NorthBound12.G before := by
   have check : ∀ j,(238:Cell)∈NorthEvents12.locks j := by decide +kernel
   exact oldLocks (check j)
 have activation : ∀ j,Core 1⊆264::(NorthEvents12.locks j).erase 238 := by decide +kernel
 have coreInside := CageFour12.shifted_inside (NorthEvents12.unique j) oldLocks owner (activation j)
 have sFacts := first.end_subset initialUnique [213] (by decide +kernel) (by decide +kernel)
 have sAt : (211:Cell)∈middle.boulders :=
   sFacts.2 (show (211:Cell)∈endGroup [213] before by rw [sGlobal];simp)
 have sKept := GhostSubset.update_subset middle t (.push 238 (.stay 264)) effect [211]
   (by decide +kernel) (by simpa using sAt)
 have sSame : update [211] (.push 238 (.stay 264))=[211] := by decide +kernel
 rw [sSame] at sKept
 have sNext : (211:Cell)∈t.state.boulders := sKept (by simp)
 have gEight := (NorthTight22812.canonical_ledgers logged completed cheap).2.2.1
 change energy p NorthBound12.G outcomes=8 at gEight
 have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthBound12.G
 change 0≤ownSlack p NorthBound12.G before at nn
 have one : slack p (.push 238 (.stay 264))=2 := by decide +kernel
 have ledger : energy p NorthBound12.G outcomes=ownSlack p NorthBound12.G before+2+
     energy p (update (endGroup NorthBound12.G before) (.push 238 (.stay 264))) after := by
   rw [shape,energy_at_split]
   simp only [projectedOutcome,if_pos owner,one]
 have budget : energy p (update (endGroup NorthBound12.G before) (.push 238 (.stay 264))) after≤6 := by omega
 exact S211SidecarCut12.impossible cut nextReached nextUnique nextSubset completed coreInside sNext budget
#print axioms impossible
end Owner1007.North238SidecarImpossible12
