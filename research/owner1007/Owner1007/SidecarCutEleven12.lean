import Owner1007.SidecarNine12
import Owner1007.AfterJSharpCash12
namespace Owner1007.SidecarCutEleven12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting Owner1007.OwnedEvents12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
theorem impossible {state final group outcomes history past pastMoves}
 (cut : AfterJSharpCash12.SidecarCut state group final outcomes)
 (reached : Trace soko1_2.board soko1_2.initial history state past pastMoves)
 (gUnique : group.Nodup) (subset : group⊆state.boulders)
 (completed : Goal final) (cheap : energy p group outcomes≤10) :False :=by
 have actualUnique:=reached.boulders_nodup (by decide +kernel)
 have atReached:=reached.append cut.first.trace
 have atUnique:=atReached.boulders_nodup (by decide +kernel)
 have old:=cut.first.end_subset actualUnique group gUnique subset
 have nextActual:=step_boulders_nodup _ _ _ _ atUnique cut.checked
 have nextUnique:=GhostSubset.update_unique cut.middle cut.actor (.push 291 (.stay 290)) cut.effect nextActual
   (endGroup group cut.before) old.1 old.2
 have nextSubset:=GhostSubset.update_subset cut.middle cut.actor (.push 291 (.stay 290)) cut.effect
   (endGroup group cut.before) old.1 old.2
 have nextReached:=atReached.append (Trace.cons cut.checked (Trace.nil cut.actor.state))
 have shift:∀i,SidecarNine12.C⊆290::(AfterJ12.locks 1 i).erase 291:=by decide +kernel
 have kept:=CageFour12.shifted_inside (AfterJ12.unique 1 cut.phase) cut.locks cut.owner (shift cut.phase)
 have heroNext:cut.actor.state.player∈SidecarNine12.region 0:=by
   rw[matches_hero cut.middle cut.actor (.push 291 (.stay 290)) cut.effect]
   exact SidecarNine12.hero291
 have later:=SidecarNine12.owned_nine cut.last nextReached
   (update (endGroup group cut.before) (.push 291 (.stay 290))) nextUnique nextSubset completed heroNext kept
 change 9≤energy p (update (endGroup group cut.before) (.push 291 (.stay 290))) cut.after at later
 have nn:=cut.first.ownSlack_nonnegative Generated.soko1_2_potential_valid group
 change 0≤ownSlack p group cut.before at nn
 have one:slack p (.push 291 (.stay 290))=2:=by decide +kernel
 have expanded:=energy_at_split p group cut.before (.push 291 (.stay 290)) cut.after
 simp only[projectedOutcome,if_pos cut.owner,one] at expanded
 have ledger:energy p group outcomes=ownSlack p group cut.before+2+
   energy p (update (endGroup group cut.before) (.push 291 (.stay 290))) cut.after:=
   (congrArg (fun os=>energy p group os) cut.shape).trans expanded
 omega
#print axioms impossible
end Owner1007.SidecarCutEleven12
