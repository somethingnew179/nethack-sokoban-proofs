import Owner1007.UpperLocalCuts11
import Owner1007.UpperReset11
import Owner1007.Upper216After11
namespace Owner1007.UpperLocalAfter11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem after_reset {state group dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut UpperZero11.paid state group dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤3)
 (goodStart : OwnedCorral11.Good UpperZero11.locks UpperZero11.region state group)
 (source : Cell) (sourceEq : cut.actor.pushSource=some source)
 (reset : UpperReset11.Reset source cut.direction) :
 OwnedCorral11.Good UpperZero11.locks UpperZero11.region cut.actor.state
   (update (endGroup group cut.beforeOutcomes) cut.headOutcome) := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have good := PairFirstCut11.quiet_good UpperZero11.closed UpperZero11.unique UpperZero11.size cut.before
   valid.1 unique inside bounded goodStart reached.holes_sublist.subset
 have selected := cut.before.logged.end_subset valid.1 group unique inside
 have beforeBound := Nat.le_trans (endGroup_length_le group cut.beforeOutcomes) bounded
 have middleHoles := (reached.append cut.before.logged.trace).holes_sublist.subset
 have avoid : ¬OwnedCorral11.PaidStep UpperReset11.useful (endGroup group cut.beforeOutcomes) cut.direction cut.actor := by
   rintro ⟨other,_,metadata,paid⟩
   have same : other=source := Option.some.inj (metadata.symm.trans sourceEq)
   exact UpperReset11.reset_not_useful reset (same ▸ paid)
 exact OwnedCorral11.step_good_except UpperReset11.useful_closed UpperZero11.unique UpperZero11.size good
   selected.2 beforeBound middleHoles cut.headChecked cut.headEffect avoid
#print axioms after_reset

theorem after216 {state group dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut UpperZero11.paid state group dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (unique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤3)
 (goodStart : OwnedCorral11.Good UpperZero11.locks UpperZero11.region state group)
 (sourceEq : cut.actor.pushSource=some 216)
 (effect : Matches cut.middle cut.actor (.push 216 (.stay 217))) :
 [191,217]⊆update (endGroup group cut.beforeOutcomes) cut.headOutcome ∧
 OwnedCorral11.Good PostCuts11.rightLocks PostCuts11.rightRegion cut.actor.state [191,217] := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have good := PairFirstCut11.quiet_good UpperZero11.closed UpperZero11.unique UpperZero11.size cut.before
   valid.1 unique inside bounded goodStart reached.holes_sublist.subset
 have selected := cut.before.logged.end_subset valid.1 group unique inside
 have beforeBound := Nat.le_trans (endGroup_length_le group cut.beforeOutcomes) bounded
 have middleHoles := (reached.append cut.before.logged.trace).holes_sublist.subset
 obtain ⟨i,_,locksInside⟩ := good
 obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
 have same : source=216 := Option.some.inj (metadata.symm.trans sourceEq)
 have before216 : 216∈endGroup group cut.beforeOutcomes := same ▸ owner
 have locked := UpperQuiet11.lock_complete i (endGroup group cut.beforeOutcomes) beforeBound locksInside 216 before216
 have row := of_decide_eq_true (List.all_eq_true.mp Upper216After11.retained191_checked i (by simp))
 have before191 : 191∈endGroup group cut.beforeOutcomes := locksInside (row.resolve_left (fun absent => absent locked))
 have headEq := GhostProjection.matches_unique cut.middle cut.actor cut.headOutcome
   (.push 216 (.stay 217)) cut.headEffect effect
 constructor
 · rw [headEq]
   simp only [update,move,if_pos before216,post]
   intro cell found
   simp only [List.mem_cons,List.not_mem_nil,or_false] at found
   rcases found with rfl|rfl
   · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide : 191≠216)).mpr before191)
   · simp
 · refine ⟨⟨0,by decide⟩,?_,?_⟩
   · have hero : cut.actor.state.player=216 := by rw [effect.2]
     rw [hero]; decide +kernel
   · exact List.Subset.refl _
#print axioms after216
end Owner1007.UpperLocalAfter11
