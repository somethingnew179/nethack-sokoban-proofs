import Owner1007.S211SidecarSix12
import Owner1007.SidecarCriticalFixed12
import Owner1007.AfterJSharpCash12
namespace Owner1007.S211SidecarCut12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
open Owner1007.SidecarCoreQuiet12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem impossible
 {state final outcomes history past pastMoves}
 (cut : AfterJSharpCash12.SidecarCut state group final outcomes)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final)
 (coreInside : Core 1⊆group) (s211 : (211:Cell)∈state.boulders)
 (cheap : energy p group outcomes≤6) :False := by
 have actualUnique := reached.boulders_nodup (by decide +kernel)
 have atReached := reached.append cut.first.trace
 have atUnique := atReached.boulders_nodup (by decide +kernel)
 have old := cut.first.end_subset actualUnique group gUnique subset
 have nextActual := step_boulders_nodup _ _ _ _ atUnique cut.checked
 have nextUnique := GhostSubset.update_unique cut.middle cut.actor (.push 291 (.stay 290)) cut.effect nextActual
   (endGroup group cut.before) old.1 old.2
 have nextSubset := GhostSubset.update_subset cut.middle cut.actor (.push 291 (.stay 290)) cut.effect
   (endGroup group cut.before) old.1 old.2
 have nextReached := atReached.append (Trace.cons cut.checked (Trace.nil cut.actor.state))
 have shift : ∀ i,Sidecar26412.locks 0⊆290::(AfterJ12.locks 1 i).erase 291 := by decide +kernel
 have kept := CageFour12.shifted_inside (AfterJ12.unique 1 cut.phase) cut.locks cut.owner (shift cut.phase)
 have heroNext : cut.actor.state.player∈Sidecar26412.region 0 := by
   rw [matches_hero cut.middle cut.actor (.push 291 (.stay 290)) cut.effect]
   decide +kernel
 have oldFour := Sidecar26412.energy_four cut.last nextReached
   (update (endGroup group cut.before) (.push 291 (.stay 290))) nextUnique nextSubset completed heroNext kept
 change 4≤energy p (update (endGroup group cut.before) (.push 291 (.stay 290))) cut.after at oldFour
 have prefixNN := cut.first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group cut.before at prefixNN
 have one : slack p (.push 291 (.stay 290))=2 := by decide +kernel
 have ledger : energy p group outcomes=ownSlack p group cut.before+2+
     energy p (update (endGroup group cut.before) (.push 291 (.stay 290))) cut.after := by
   have expanded := energy_at_split p group cut.before (.push 291 (.stay 290)) cut.after
   simp only [projectedOutcome,if_pos cut.owner,one] at expanded
   exact (congrArg (fun os=>energy p group os) cut.shape).trans expanded
 have zeroGroup : ownSlack p group cut.before=0 := by omega
 have coreActual := List.Subset.trans coreInside subset
 have mono := cut.first.ownSlack_mono Generated.soko1_2_potential_valid actualUnique
   (Core 1) group (core_unique 1) gUnique coreActual subset coreInside
 change ownSlack p (Core 1) cut.before≤ownSlack p group cut.before at mono
 have coreNN := cut.first.ownSlack_nonnegative Generated.soko1_2_potential_valid (Core 1)
 change 0≤ownSlack p (Core 1) cut.before at coreNN
 have zeroCore : ownSlack p (Core 1) cut.before=0 := by omega
 have coreTag := cut.fixedBefore (Core 1) (by decide +kernel)
 have coreQuiet := SidecarCriticalFixed12.quiet_of_zero_slack p (Core 1) cut.before coreTag zeroCore
 have sQuiet := SidecarCriticalBranch12.stationary211 cut.first reached 1 coreActual coreQuiet
 have sTag := no_push_unchanged [211] cut.before sQuiet
 have sFacts := cut.first.end_subset actualUnique [211] (by decide +kernel) (by simpa using s211)
 have sAt : (211:Cell)∈cut.middle.boulders :=
   sFacts.2 (show (211:Cell)∈endGroup [211] cut.before by rw [sTag];simp)
 have sKept := GhostSubset.update_subset cut.middle cut.actor (.push 291 (.stay 290)) cut.effect
   [211] (by decide +kernel) (by simpa using sAt)
 have sSame : update [211] (.push 291 (.stay 290))=[211] := by decide +kernel
 rw [sSame] at sKept
 have sNext : (211:Cell)∈cut.actor.state.boulders := sKept (by simp)
 have strongHero : cut.actor.state.player∈S211SidecarSix12.region 0 := by
   rw [matches_hero cut.middle cut.actor (.push 291 (.stay 290)) cut.effect]
   exact S211SidecarSix12.hero291
 have strongInside : S211SidecarSix12.C⊆update (endGroup group cut.before) (.push 291 (.stay 290)) := by
   change Sidecar26412.locks 0⊆update (endGroup group cut.before) (.push 291 (.stay 290))
   exact kept
 have six := S211SidecarSix12.owned_six cut.last nextReached
   (update (endGroup group cut.before) (.push 291 (.stay 290))) nextUnique nextSubset
   completed strongHero strongInside sNext
 change 6≤energy p (update (endGroup group cut.before) (.push 291 (.stay 290))) cut.after at six
 omega
#print axioms impossible
end Owner1007.S211SidecarCut12
