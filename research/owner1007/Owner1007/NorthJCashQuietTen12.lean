import Owner1007.AfterJCashQuietEight12
import Owner1007.NorthTight22812
namespace Owner1007.NorthJCashQuietTen12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.AfterJ12 Owner1007.AfterJBound12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

/-- The tight canonical budget activates the cash filter without adding
any separate energy hypothesis about the actual continuation. -/
theorem split {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (gBudget : energy p NorthBound12.G outcomes≤10) (kind : Fin 2)
 {beforeDirs beforePushes beforeMoves before middle t after afterDirs afterPushes afterMoves}
 (shape : outcomes=before++headOutcome kind::after)
 (first : Logged soko1_2.board FirstSplit12.afterN beforeDirs middle beforePushes beforeMoves before)
 (checked : step soko1_2.board middle .south=some t)
 (effect : Matches middle t (headOutcome kind))
 (last : Logged soko1_2.board t.state afterDirs final afterPushes afterMoves after)
 (i : Fin 5) (locksInside : NorthEvents12.locks i⊆endGroup NorthBound12.G before) :
 ∃ bd bp bm between mid dir actor source ending rest ad ap am,∃ j : Fin 5,
 after=between++.push source ending::rest ∧
 Logged soko1_2.board t.state bd mid bp bm between ∧
 step soko1_2.board mid dir=some actor ∧Matches mid actor (.push source ending) ∧
 Logged soko1_2.board actor.state ad final ap am rest ∧
 mid.player∈region kind j ∧
 locks kind j⊆endGroup (update (endGroup NorthBound12.G before) (headOutcome kind)) between ∧
 source∈endGroup (update (endGroup NorthBound12.G before) (headOutcome kind)) between ∧
 AfterJ12.paid kind source dir ∧
 (∀small : List Cell,small⊆fixed kind→endGroup small between=small) ∧ownPushes (fixed kind) between=0 ∧
 source≠265 ∧(source=291→kind=1) := by
 have middleReached := NorthBound12.north_reached.append first.trace
 have actual := middleReached.boulders_nodup (by decide +kernel)
 have old := first.end_subset (by decide +kernel) NorthBound12.G (by decide +kernel) (by decide +kernel)
 have nextActual := step_boulders_nodup _ _ _ _ actual checked
 have nextUnique := GhostSubset.update_unique middle t (headOutcome kind) effect nextActual
   (endGroup NorthBound12.G before) old.1 old.2
 have nextSubset := GhostSubset.update_subset middle t (headOutcome kind) effect
   (endGroup NorthBound12.G before) old.1 old.2
 have nextReached := middleReached.append (Trace.cons checked (Trace.nil t.state))
 have owner : startSource kind∈endGroup NorthBound12.G before := locksInside (source_inside kind i)
 have erased := GhostSubset.erase_subset locksInside (NorthEvents12.unique i) (startSource kind)
 have nextLocks : locks kind i⊆update (endGroup NorthBound12.G before) (headOutcome kind) := by
   simp only [headOutcome,update,move,if_pos owner,post]
   exact List.Subset.trans (activation kind i) (List.cons_subset_cons (startDest kind) erased)
 have heroNext : t.state.player=startSource kind := matches_hero middle t (headOutcome kind) effect
 have nextHero : t.state.player∈region kind i := by
   rw [heroNext]
   change startSource kind∈NorthEvents12.region i++[startSource kind]
   exact List.mem_append_right _ (by simp)
 have eight := gBudget
 have nn := first.ownSlack_nonnegative Generated.soko1_2_potential_valid NorthBound12.G
 change 0≤ownSlack p NorthBound12.G before at nn
 have ledger : energy p NorthBound12.G outcomes=ownSlack p NorthBound12.G before+2+
     energy p (update (endGroup NorthBound12.G before) (headOutcome kind)) after := by
   rw [shape,energy_at_split]
   simp only [headOutcome,projectedOutcome,if_pos owner]
   change ownSlack p NorthBound12.G before+slack p (headOutcome kind)+
     energy p (update (endGroup NorthBound12.G before) (headOutcome kind)) after=_
   rw [first_price]
   rfl
 have budget : energy p (update (endGroup NorthBound12.G before) (headOutcome kind)) after≤8 := by omega
 exact AfterJCashQuietEight12.split last nextReached completed kind _ nextUnique nextSubset i nextHero nextLocks budget
#print axioms split
end Owner1007.NorthJCashQuietTen12
