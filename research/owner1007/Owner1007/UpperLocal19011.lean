import Owner1007.UpperLocalAfter11
import Owner1007.Upper190History11
namespace Owner1007.UpperLocal19011
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem stationary_before_west {state group dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut UpperZero11.paid state group dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤3)
 (goodStart : OwnedCorral11.Good UpperZero11.locks UpperZero11.region state group)
 (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.west) :
 ownPushes [137] cut.beforeOutcomes=0 ∧ ownPushes [139] cut.beforeOutcomes=0 := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have good := PairFirstCut11.quiet_good UpperZero11.closed UpperZero11.unique UpperZero11.size cut.before
   valid.1 unique inside bounded goodStart reached.holes_sublist.subset
 have beforeBound := Nat.le_trans (endGroup_length_le group cut.beforeOutcomes) bounded
 obtain ⟨i,heroInside,locksInside⟩ := good
 obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
 have same : source=190 := Option.some.inj (metadata.symm.trans sourceEq)
 have present : 190 ∈ endGroup group cut.beforeOutcomes := same ▸ owner
 have locked := UpperQuiet11.lock_complete i (endGroup group cut.beforeOutcomes) beforeBound locksInside 190 present
 have adjacent := Upper190History11.push_adjacent cut.headChecked sourceEq
 rw [directionEq] at adjacent
 have hero := ActorPrices11.support_of_check 190 cut.middle.player .west 191
   (by decide +kernel) (step_player_clear _ _ _ _ cut.headChecked).1 adjacent
 have hero191 : 191 ∈ UpperZero11.region i := by simpa only [hero] using heroInside
 have row := of_decide_eq_true (List.all_eq_true.mp Upper190History11.phase190_checked i (by simp))
 have phase : i.val=12 := by
   rcases row with outside | outside | phase
   · exact False.elim (outside locked)
   · exact False.elim (outside hero191)
   · exact phase
 have index : i=⟨12,by decide⟩ := Fin.ext phase
 have seen137 : 137 ∈ endGroup group cut.beforeOutcomes := locksInside (by rw [index]; decide +kernel)
 have seen139 : 139 ∈ endGroup group cut.beforeOutcomes := locksInside (by rw [index]; decide +kernel)
 exact ⟨cut.before.stationary UpperZero11.closed valid.1 unique inside bounded goodStart reached.holes_sublist.subset
     137 (by simp) seen137,
   cut.before.stationary UpperZero11.closed valid.1 unique inside bounded goodStart reached.holes_sublist.subset
     139 (by simp) seen139⟩
#print axioms stationary_before_west
end Owner1007.UpperLocal19011
