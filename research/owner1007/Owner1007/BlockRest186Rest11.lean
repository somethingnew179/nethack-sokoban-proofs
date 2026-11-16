import Owner1007.BlockRestNorth11
import Owner1007.Spare315Rest11
namespace Owner1007.BlockRest186Rest11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem count_zero {beforeDirs state beforePushes beforeMoves before dirs middle pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs middle pushes moves outcomes)
 (suffix : Logged soko1_1.board middle lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest ((before++outcomes)++last)<2)
 (present : 186∈state.boulders) (stationary : ownPushes [186] outcomes=0)
 (group : List Cell) : PaidCount11.count FirstRest18711.paid group dirs outcomes=0:=by
 rcases first_cut_or_quiet (paid:=FirstRest18711.paid) logged group with found|quiet
 ·obtain ⟨cut⟩:=found
  have beforeZero : ownPushes [186] cut.beforeOutcomes=0:=by
   have same : ownPushes [186] (cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)=0:=by
    rw [←cut.outcomesEq];exact stationary
   rw [ownPushes_append] at same
   omega
  have fixed:=no_push_unchanged [186] cut.beforeOutcomes beforeZero
  have facts:=cut.before.logged.end_subset (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1
   [186] (by decide) (by simpa using present)
  have retained : 186∈cut.middle.boulders:=facts.2 (by rw [fixed];simp)
  obtain ⟨source,owner,metadata,at213,north⟩:=cut.headPaid
  have source213 : cut.actor.pushSource=some 213:=by simpa only [at213] using metadata
  have checked : step soko1_1.board cut.middle .north=some cut.actor:=by simpa only [north] using cut.headChecked
  let current:=first.append cut.before.logged
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect source213
    (show pushTargets soko1_1.board 213 .north=[187] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 213 (.stay 187)):=by simpa only [headEq] using cut.headEffect
  let one : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome]:=
   .cons cut.headChecked cut.headEffect (.nil _)
  have physical : [186,187]⊆cut.actor.state.boulders:=by
   rw [effect.2]
   intro c member
   rcases List.mem_cons.mp member with rfl|later
   ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide : (186:Cell)≠213)).mpr retained)
   ·have same:c=187:=List.mem_singleton.mp later
    subst c;exact List.mem_cons_self
  have sameOutcomes : ((before++cut.beforeOutcomes)++[cut.headOutcome])++(cut.afterOutcomes++last)=(before++outcomes)++last:=by
   simpa only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
    congrArg (fun xs=>before++xs++last) cut.outcomesEq.symm
  have restHere : energy soko1_1.initial final UpperBudget11.Rest
    (((before++cut.beforeOutcomes)++[cut.headOutcome])++(cut.afterOutcomes++last))<2:=by
   rw [sameOutcomes];exact restCap
  exact False.elim (Spare315Rest11.frozen_pair (current.append one) (cut.after.append suffix) completed restHere
   [186,187] (locked_of_check _ [186,187] (by decide +kernel)) (by decide) rfl physical (by decide))
 ·exact FirstRest18711.quiet_count_zero quiet
#print axioms count_zero
end Owner1007.BlockRest186Rest11
