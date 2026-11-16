import Owner1007.RightEarlyQuiet11
import Owner1007.InwardCurrentTripleEight11
import Owner1007.UpperShaftGate11
import Owner1007.First137RestAnywhere11
import Owner1007.Tight32511
namespace Owner1007.RightEarlyWest11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11 Owner1007.UpperBudget11
open Owner1007.RightEarlyWords11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem inward_eight {state final : State} {t : Transition} {dir : Dir} {source : Cell}
 {beforeDirs afterDirs : List Dir} {beforePushes beforeMoves afterPushes afterMoves : Nat} {before after : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state dir=some t) (effect : Matches state t (.push source (.stay 138)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (selected : [137,139,191,193]⊆endGroup U6 before) (i : Fin 4)
 (bridge : Inward191Eight11.locks i⊆update [137,139,191,193] (.push source (.stay 138)))
 (mate : 193∈update [137,139,191,193] (.push source (.stay 138)))
 (hero : source∈Inward191Eight11.region i) :
 8≤energy soko1_1.initial final U6 (before++.push source (.stay 138)::after):=by
 have afterSelected:=update_mono [137,139,191,193] (endGroup U6 before) (by decide) selected (.push source (.stay 138))
 let headLogged : Logged soko1_1.board state [dir] t.state t.pushCost 1 [.push source (.stay 138)]:=
   .cons head effect (.nil _)
 let extended:=first.append headLogged
 have next : Inward191Eight11.locks i⊆endGroup U6 (before++[.push source (.stay 138)]):=by
   rw [endGroup_append]
   exact List.Subset.trans bridge afterSelected
 have owns193 : 193∈endGroup U6 (before++[.push source (.stay 138)]):=by
   rw [endGroup_append]
   exact afterSelected mate
 have good : OwnedCorral11.Good Inward191Eight11.locks Inward191Eight11.region t.state
     (endGroup U6 (before++[.push source (.stay 138)])):=by
   refine ⟨i,?_,next⟩
   have same : t.state.player=source:=by rw [effect.2]
   rw [same];exact hero
 have reserve:=InwardCurrentTripleEight11.reserve_eight extended last completed good owns193
 simpa only [List.append_assoc,List.singleton_append] using reserve

theorem first_west {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (upperCheap : energy soko1_1.initial final U6 outcomes<8)
 (restCheap : energy soko1_1.initial final Rest outcomes<2) :
 ∃cut : FirstCut paid soko1_1.initial G dirs final pushes moves outcomes,
   cut.actor.pushSource=some 190∧cut.direction=.west∧cut.headOutcome=.push 190 (.stay 189)∧
   endGroup [191] cut.beforeOutcomes=[190]∧
   ownPushes [137] cut.beforeOutcomes=0∧ownPushes [139] cut.beforeOutcomes=0:=by
 have wholeGone:=Upper216Eight11.all_gone_eight logged completed upperCheap
 have subsetGone:=logged.end_mono (by decide) G U6 (by decide) (by decide) (by decide)
 rw [wholeGone] at subsetGone
 have gone : endGroup G outcomes=[]:=List.eq_nil_iff_forall_not_mem.mpr (by intro c h;simpa using subsetGone h)
 have good : OwnedCorral11.Good locks region soko1_1.initial G:=⟨0,initialHero,by decide⟩
 obtain ⟨cut⟩:=Upper216Eight11.first_any closed unique (by decide +kernel)
   logged (by decide) (by decide) (by decide) good (by simp) gone
 obtain ⟨i,heroBefore,selected,tagQ,tagR,zero137,zero139⟩:=quiet_packet cut.before
 have beforeFacts:=cut.before.logged.end_subset (by decide) G (by decide) (by decide)
 have beforeBound:=endGroup_length_le G cut.beforeOutcomes
 change (endGroup G cut.beforeOutcomes).length≤4 at beforeBound
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
 have nextReached:=cut.before.logged.trace.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have nextFacts:=Upper216Eight11.next_facts cut (Trace.nil _) (by decide) (by decide) (by decide)
 have nextGone:=Upper216Eight11.tail_gone cut gone
 have beforeUpper:=cut.before.logged.end_subset (by decide) U6 (by decide) (by decide)
 have included:=end_subset_selected cut.before.logged (by decide) G U6 (by decide) (by decide) (by decide) (by decide)
 obtain ⟨source,owner,metadata,shape⟩:=head_shape i heroBefore selected beforeFacts.2 beforeBound cut.headChecked cut.headPaid
 rcases shape with ⟨gates,phaseZero⟩|⟨rfl,west,q190⟩|⟨rfl,north,q190⟩|
   ⟨rfl,east,q191,r193⟩|⟨rfl,east,r193⟩|lockedPhase
 ·have iZero : i=0:=Fin.ext phaseZero
  rw [iZero] at selected
  have upperFour : [137,139,191,193]⊆endGroup U6 cut.beforeOutcomes:=List.Subset.trans selected included
  rcases gates with rfl|rfl
  ·rcases gate_direction (show 137∈([137,139]:List Cell) by simp) cut.headChecked metadata with east|west
   ·have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
    have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
      (show pushTargets soko1_1.board 137 .east=[138] by decide +kernel) (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
    have effect : Matches cut.middle cut.actor (.push 137 (.stay 138)):=by simpa only [headEq] using cut.headEffect
    have reserve:=inward_eight cut.before.logged checked effect cut.after completed upperFour 0
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have eq:=cut.outcomesEq
    rw [headEq] at eq
    rw [eq] at upperCheap
    omega
   ·have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
    have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
      (show pushTargets soko1_1.board 137 .west=[136] by decide +kernel) (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
    have effect : Matches cut.middle cut.actor (.push 137 (.stay 136)):=by simpa only [headEq] using cut.headEffect
    have reserve:=First137RestAnywhere11.rest_two cut.before.logged checked effect cut.after completed zero137
    have eq:=cut.outcomesEq
    rw [headEq] at eq
    rw [←eq] at reserve
    omega
  ·rcases gate_direction (show 139∈([137,139]:List Cell) by simp) cut.headChecked metadata with east|west
   ·have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
    have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
      (show pushTargets soko1_1.board 139 .east=[140] by decide +kernel) (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
    have effect : Matches cut.middle cut.actor (.push 139 (.stay 140)):=by simpa only [headEq] using cut.headEffect
    have whole141:=UpperEightBudget11.cheap_others_six logged completed upperCheap 141 (by decide)
    have bound:=prefix_energy_le cut.before.logged (Logged.cons cut.headChecked cut.headEffect cut.after) [141] (by decide) (by decide)
    rw [←cut.outcomesEq] at bound
    have cheap141 : energy soko1_1.initial cut.middle [141] cut.beforeOutcomes<6:=by omega
    have survives:=StationaryExitSix11.survives139 cut.before.logged checked effect cut.after zero139 cheap141
    have whole : endGroup [139] outcomes≠[]:=by rw [cut.outcomesEq,headEq];exact survives
    exact False.elim (UpperEightExit11.survivor_eight_absurd logged completed upperCheap 139 (by simp) whole)
   ·have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
    have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
      (show pushTargets soko1_1.board 139 .west=[138] by decide +kernel) (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
    have effect : Matches cut.middle cut.actor (.push 139 (.stay 138)):=by simpa only [headEq] using cut.headEffect
    have reserve:=inward_eight cut.before.logged checked effect cut.after completed upperFour 1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have eq:=cut.outcomesEq
    rw [headEq] at eq
    rw [eq] at upperCheap
    omega
 ·have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 190 .west=[189] by decide +kernel) (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
  rw [q190] at tagQ
  exact ⟨cut,metadata,west,headEq,tagQ,zero137,zero139⟩
 ·have checked : step soko1_1.board cut.middle .north=some cut.actor:=by simpa only [north] using cut.headChecked
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 190 .north=[164] by decide +kernel) (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 190 (.stay 164)):=by simpa only [headEq] using cut.headEffect
  have eq:=cut.outcomesEq
  rw [headEq] at eq
  have upper : energy soko1_1.initial final U6 (cut.beforeOutcomes++.push 190 (.stay 164)::cut.afterOutcomes)<8:=by rw [←eq];exact upperCheap
  have rest : energy soko1_1.initial final Rest (cut.beforeOutcomes++.push 190 (.stay 164)::cut.afterOutcomes)<2:=by rw [←eq];exact restCheap
  rcases UpperShaftGate11.gate_moved_before_north cut.before.logged checked effect cut.after completed upper rest with positive|positive <;> omega
 ·have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 191 .east=[192] by decide +kernel) (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
  have pairBefore : [191,193]⊆endGroup G cut.beforeOutcomes:=by
    apply List.Subset.trans (show [191,193]⊆locks i from ?_) selected
    simp only [locks,q191,r193]
    decide
  have afterPair:=update_mono [191,193] (endGroup G cut.beforeOutcomes) (by decide) pairBefore cut.headOutcome
  have owned : [192,193]⊆Upper216Eight11.next cut:=by
    change [192,193]⊆update (endGroup G cut.beforeOutcomes) cut.headOutcome
    rw [headEq] at afterPair ⊢
    exact List.Subset.trans (by decide) afterPair
  exact False.elim (Upper216Eight11.frozen_absurd cut.after
    (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant nextReached).1 nextFacts.1 nextFacts.2.1
    (Owner1007.locked_of_check _ [192,193] (by decide +kernel)) (List.Subset.trans owned nextFacts.2.1)
    (show 192∈[192,193] by decide) (owned (by decide)) nextGone)
 ·have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 193 .east=[194] by decide +kernel) (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 193 (.stay 194)):=by simpa only [headEq] using cut.headEffect
  have owned : 194∈Upper216Eight11.next cut:=by
    change 194∈update (endGroup G cut.beforeOutcomes) cut.headOutcome
    rw [headEq]
    simp only [update,move,if_pos owner,post,List.mem_cons]
    exact Or.inl trivial
  have physical : [194]⊆cut.actor.state.boulders:=by simpa using nextFacts.2.1 owned
  exact False.elim (Upper216Eight11.frozen_absurd cut.after
    (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant nextReached).1 nextFacts.1 nextFacts.2.1
    (Owner1007.locked_of_check _ [194] (by decide +kernel)) physical (by simp) owned nextGone)
 ·have iFour : i=4:=Fin.ext lockedPhase
  rw [iFour] at selected
  have owned : [191,192]⊆endGroup G cut.beforeOutcomes:=List.Subset.trans (by decide) selected
  have suffix:=Logged.cons cut.headChecked cut.headEffect cut.after
  have currentGone : endGroup (endGroup G cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=[]:=by
    have same:=gone
    rw [cut.outcomesEq,endGroup_append] at same
    exact same
  exact False.elim (Upper216Eight11.frozen_absurd suffix valid.1 beforeFacts.1 beforeFacts.2
    (Owner1007.locked_of_check _ [191,192] (by decide +kernel)) (List.Subset.trans owned beforeFacts.2)
    (show 191∈[191,192] by decide) (owned (by decide)) currentGone)

theorem tight_first_west {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325) :
 ∃cut : FirstCut paid soko1_1.initial G dirs final pushes moves outcomes,
   cut.actor.pushSource=some 190∧cut.direction=.west∧cut.headOutcome=.push 190 (.stay 189)∧
   endGroup [191] cut.beforeOutcomes=[190]∧
   ownPushes [137] cut.beforeOutcomes=0∧ownPushes [139] cut.beforeOutcomes=0:=by
 have budget:=Tight32511.budgets logged completed cheap
 exact first_west logged completed (by omega) (by omega)
#print axioms first_west
#print axioms tight_first_west
end Owner1007.RightEarlyWest11

