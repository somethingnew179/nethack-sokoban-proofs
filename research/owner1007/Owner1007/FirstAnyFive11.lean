import Owner1007.FirstAnyFive11Helpers
namespace Owner1007.FirstAnyFive11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem first_west {state final : State} {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤6)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)<2)
 (zero137 : ownPushes [137] before=0) (zero139 : ownPushes [139] before=0)
 (prefixFour : 4≤energy soko1_1.initial state UpperBudget11.U6 before)
 (inside : K⊆state.boulders) (selected : U⊆endGroup UpperBudget11.U6 before)
 (gone : endGroup K outcomes=[]) :
 ∃cut : FirstCut (fun _ _=>True) state K dirs final pushes moves outcomes,
  ownPushes K cut.beforeOutcomes=0 ∧ cut.actor.pushSource=some 185 ∧ cut.direction=.west ∧
   Matches cut.middle cut.actor (.push 185 (.stay 184)):=by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have found : Nonempty (FirstCut (fun _ _=>True) state K dirs final pushes moves outcomes):=by
  rcases first_cut_or_quiet logged K with found|quiet
  ·exact found
  ·have same:=no_push_unchanged K outcomes (quiet_zero quiet)
   rw [gone] at same
   exact False.elim (by change []=[137,139,185,187,189] at same;contradiction)
 obtain ⟨cut⟩:=found
 have quietZero:=quiet_zero cut.before
 have fixed:=no_push_unchanged K cut.beforeOutcomes quietZero
 have beforeFacts:=cut.before.logged.end_subset valid.1 K (by decide) inside
 have currentInside : K⊆cut.middle.boulders:=by simpa only [fixed] using beforeFacts.2
 let current:=first.append cut.before.logged
 have currentValid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant current.trace
 have allEffects : (before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes=before++outcomes:=by rw [List.append_assoc,←cut.outcomesEq]
 have currentUpper : energy soko1_1.initial final UpperBudget11.U6 ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)≤6:=by rw [allEffects];exact upperCap
 have currentRest : energy soko1_1.initial final UpperBudget11.Rest ((before++cut.beforeOutcomes)++cut.headOutcome::cut.afterOutcomes)<2:=by rw [allEffects];exact restCap
 have monotone:=prefix_energy_le first cut.before.logged UpperBudget11.U6 (by decide) (by decide)
 have currentPrefix : 4≤energy soko1_1.initial cut.middle UpperBudget11.U6 (before++cut.beforeOutcomes):=by omega
 have currentZero : ∀c∈([137,139]:List Cell),ownPushes [c] (before++cut.beforeOutcomes)=0:=by
  intro c member
  have localZero:=LeftQuietIdentity11.subset_zero [c] K cut.beforeOutcomes (by
   intro a h
   have same:=List.mem_singleton.mp h
   subst a
   exact (show ([137,139]:List Cell)⊆K by decide) member) quietZero
  have initialZero : ownPushes [c] before=0:=by
   rcases (show c=137∨c=139 by simpa using member) with rfl|rfl
   ·exact zero137
   ·exact zero139
  rw [ownPushes_append,no_push_unchanged _ _ initialZero,initialZero,localZero]
 have currentSelected : U⊆endGroup UpperBudget11.U6 (before++cut.beforeOutcomes):=by
  have initialFacts:=first.end_subset (by decide) UpperBudget11.U6 (by decide) (by decide)
  have localUZero:=LeftQuietIdentity11.subset_zero U K cut.beforeOutcomes (by decide) quietZero
  have localUFixed:=no_push_unchanged U cut.beforeOutcomes localUZero
  have mono:=cut.before.logged.end_mono valid.1 U (endGroup UpperBudget11.U6 before) (by decide)
   (List.Subset.trans selected initialFacts.2) selected
  rw [localUFixed] at mono
  rw [endGroup_append]
  exact mono
 have afterFacts:=Upper216Eight11.next_facts cut first.trace (by decide) inside (by decide)
 have afterGone:=Upper216Eight11.tail_gone cut gone
 have afterReached:=current.trace.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have frozenCase : ∀pair : List Cell,∀a : Cell,Locked soko1_1.board pair→a∈pair→pair⊆Upper216Eight11.next cut→False:=by
  intro pair a locked member subset
  exact Upper216Eight11.frozen_absurd cut.after (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant afterReached).1
   afterFacts.1 afterFacts.2.1 locked (List.Subset.trans subset afterFacts.2.1) member (subset member) afterGone
 obtain ⟨source,owner,metadata,_⟩:=cut.headPaid
 have member : source∈K:=by rw [fixed] at owner;exact owner
 have dirs:=directions currentInside member cut.headChecked metadata
 have sources : source=137∨source=139∨source=185∨source=187∨source=189:=by simpa [K] using member
 rcases sources with rfl|rfl|rfl|rfl|rfl
 ·rcases dirs with east|west
  ·have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 137 .east=[138] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 137 (.stay 138)):=by simpa only [headEq] using cut.headEffect
   rw [headEq] at currentUpper currentRest
   have noCompletion:=inward_impossible current 0 checked effect cut.after completed
    (by change energy soko1_1.initial final UpperBudget11.U6 ((before++cut.beforeOutcomes)++.push 137 (.stay 138)::cut.afterOutcomes)≤8;omega) currentRest (currentZero 139 (by simp)) currentInside (by
     change endGroup (update K (.push 137 (.stay 138))) cut.afterOutcomes=[]
     simpa only [Upper216Eight11.next,fixed,headEq] using afterGone)
   exact False.elim noCompletion
  ·have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 137 .west=[136] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 137 (.stay 136)):=by simpa only [headEq] using cut.headEffect
   have two:=First137RestAnywhere11.rest_two current checked effect cut.after completed (currentZero 137 (by simp))
   rw [headEq] at currentRest
   omega
 ·rcases dirs with east|west
  ·have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 139 .east=[140] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 139 (.stay 140)):=by simpa only [headEq] using cut.headEffect
   rw [headEq] at currentUpper
   exact False.elim (Gate139EastImpossible11.impossible current checked effect cut.after completed (by omega) (currentZero 139 (by simp)))
  ·have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 139 .west=[138] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 139 (.stay 138)):=by simpa only [headEq] using cut.headEffect
   rw [headEq] at currentUpper currentRest
   have noCompletion:=inward_impossible current 1 checked effect cut.after completed
    (by change energy soko1_1.initial final UpperBudget11.U6 ((before++cut.beforeOutcomes)++.push 139 (.stay 138)::cut.afterOutcomes)≤8;omega) currentRest (currentZero 137 (by simp)) currentInside (by
     change endGroup (update K (.push 139 (.stay 138))) cut.afterOutcomes=[]
     simpa only [Upper216Eight11.next,fixed,headEq] using afterGone)
   exact False.elim noCompletion
 ·rcases dirs with east|west
  ·have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 185 .east=[186] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   exact False.elim (frozenCase [186,187] 186 (locked_of_check _ _ (by decide +kernel)) (by decide)
    (by change _⊆update (endGroup K cut.beforeOutcomes) cut.headOutcome;rw [fixed,headEq];decide +kernel))
  ·have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 185 .west=[184] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 185 (.stay 184)):=by simpa only [headEq] using cut.headEffect
   exact ⟨cut,quietZero,metadata,west,effect⟩
 ·rcases dirs with east|west
  ·have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 187 .east=[188] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   exact False.elim (frozenCase [188,189] 188 (locked_of_check _ _ (by decide +kernel)) (by decide)
    (by change _⊆update (endGroup K cut.beforeOutcomes) cut.headOutcome;rw [fixed,headEq];decide +kernel))
  ·have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 187 .west=[186] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   exact False.elim (frozenCase [185,186] 185 (locked_of_check _ _ (by decide +kernel)) (by decide)
    (by change _⊆update (endGroup K cut.beforeOutcomes) cut.headOutcome;rw [fixed,headEq];decide +kernel))
 ·rcases dirs with east|west
  ·have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 189 .east=[190] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 189 (.stay 190)):=by simpa only [headEq] using cut.headEffect
   let one : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome]:=.cons cut.headChecked cut.headEffect (.nil _)
   let extended:=current.append one
   have sequence : ((before++cut.beforeOutcomes)++[cut.headOutcome])++cut.afterOutcomes=before++outcomes:=by
    simpa only [List.append_assoc,List.singleton_append] using allEffects
   have afterUpper : energy soko1_1.initial final UpperBudget11.U6 (((before++cut.beforeOutcomes)++[cut.headOutcome])++cut.afterOutcomes)≤8:=by rw [sequence];omega
   have afterRest : energy soko1_1.initial final UpperBudget11.Rest (((before++cut.beforeOutcomes)++[cut.headOutcome])++cut.afterOutcomes)≤4:=by rw [sequence];omega
   have afterZero : ∀c∈([137,139]:List Cell),ownPushes [c] ((before++cut.beforeOutcomes)++[cut.headOutcome])=0:=by
    intro c h
    have z:=currentZero c h
    rw [ownPushes_append,no_push_unchanged _ _ z,z]
    rw [headEq]
    have ne : (189:Cell)∉[c]:=by
     rcases (show c=137∨c=139 by simpa using h) with rfl|rfl <;> decide
    simp [ownPushes,ownPush,ne]
   have afterPrefix : 4≤energy soko1_1.initial cut.actor.state UpperBudget11.U6 ((before++cut.beforeOutcomes)++[cut.headOutcome]):=by
    have nn:=prefix_energy_le current one UpperBudget11.U6 (by decide) (by decide)
    omega
   have factsU:=current.end_subset (by decide) UpperBudget11.U6 (by decide) (by decide)
   have lifted:=update_mono U (endGroup UpperBudget11.U6 (before++cut.beforeOutcomes)) (by decide) currentSelected cut.headOutcome
   have afterSelected : Q190Upper11.locks 0⊆endGroup UpperBudget11.U6 ((before++cut.beforeOutcomes)++[cut.headOutcome]):=by
    rw [endGroup_append]
    change _⊆update (endGroup UpperBudget11.U6 (before++cut.beforeOutcomes)) cut.headOutcome
    apply List.Subset.trans (l₂:=update U cut.headOutcome) _ lifted
    rw [headEq]
    decide +kernel
   have afterHero : cut.actor.state.player∈Q190Upper11.region 0:=by rw [effect.2];change 189∈Q190Upper11.region 0;decide +kernel
   have eight:=Q190Upper11.upper_eight extended cut.after completed afterUpper afterRest
    (afterZero 137 (by simp)) (afterZero 139 (by simp)) afterPrefix 0 afterSelected afterHero
   rw [sequence] at eight
   omega
  ·have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
   have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 189 .west=[188] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
   exact False.elim (frozenCase [187,188] 187 (locked_of_check _ _ (by decide +kernel)) (by decide)
    (by change _⊆update (endGroup K cut.beforeOutcomes) cut.headOutcome;rw [fixed,headEq];decide +kernel))
#print axioms first_west
end Owner1007.FirstAnyFive11
