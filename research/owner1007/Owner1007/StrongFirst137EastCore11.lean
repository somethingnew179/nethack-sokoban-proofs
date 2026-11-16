import Owner1007.Row133135137Proof11
import Owner1007.TightSurvivors11
import Owner1007.First137East11
namespace Owner1007.Row13313513711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem canonical_no_west_with
 (closure : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 137 (.stay 136)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (stationary : ownPushes [137] before=0)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++.push 137 (.stay 136)::after)≤8)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++.push 137 (.stay 136)::after)≤4) : False := by
 let logged := first.append (Logged.cons head effect last)
 have gone : endGroup G (before++.push 137 (.stay 136)::after)=[] := by
  apply TightSurvivors11.all_nil logged (by decide) G (by decide) (by decide)
  intro cell member
  simp only [G,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl
  ·exact TightSurvivors11.singleton_nil logged completed UpperBudget11.Rest (by decide) (by decide) (by decide) 4 restCap 133 (by decide) (by decide +kernel)
  ·exact TightSurvivors11.singleton_nil logged completed UpperBudget11.Rest (by decide) (by decide) (by decide) 4 restCap 135 (by decide) (by decide +kernel)
  ·exact TightSurvivors11.singleton_nil logged completed UpperBudget11.U6 (by decide) (by decide) (by decide) 8 upperCap 137 (by decide) (by decide +kernel)
 exact no_first_west_with closure first head effect last stationary gone
#print axioms canonical_no_west_with
end Owner1007.Row13313513711
namespace Owner1007.StrongFirst137East11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.First137East11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem chronological_with
 (closure : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes Row13313513711.locks Row13313513711.region Row13313513711.paid)
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 outcomes≤8)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest outcomes≤4) :
 ∃cut : FirstCut paid soko1_1.initial [137] dirs final pushes moves outcomes,
   cut.actor.pushSource=some 137 ∧ cut.direction=.east ∧ cut.headOutcome=.push 137 (.stay 138) ∧
   ownPushes [137] cut.beforeOutcomes=0 ∧ cut.middle.holes=soko1_1.initial.holes := by
 have found : Nonempty (FirstCut paid soko1_1.initial [137] dirs final pushes moves outcomes):=by
   rcases first_cut_or_quiet (paid:=paid) logged [137] with event|quiet
   · exact event
   · have zero:=quiet.fixed (by simp :137∈([137] :List Cell)) (by intro d;trivial)
     have nofill:=FirstFill13711.no_fill_before137_moves logged zero
     have empty : final.holes=[]:=completed
     exact False.elim ((show soko1_1.initial.holes≠[] by decide +kernel) (nofill.symm.trans empty))
 obtain ⟨cut⟩:=found
 have stationary:=cut.before.fixed (by simp :137∈([137] :List Cell)) (by intro d;trivial)
 have tag:=no_push_unchanged [137] cut.beforeOutcomes stationary
 obtain ⟨source,owner,metadata,_⟩:=cut.headPaid
 rw [tag] at owner
 have sourceEq : source=137:=List.mem_singleton.mp owner
 subst source
 have adjacent:=PairPost11.source_adjacent cut.headChecked metadata
 have floor:=(step_player_clear _ _ _ _ cut.headChecked).1
 have behind:=Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked cut.middle.player floor cut.direction 137 adjacent
 have row:=List.all_eq_true.mp head_checked cut.direction (Geometry.all_directions cut.direction)
 simp only [headCheck,behind] at row
 have unblocked:=WestRankHead11.source_unblocked cut.headChecked metadata (show ([]:List Cell)⊆cut.middle.boulders by simp)
 have direction : cut.direction=.east ∨cut.direction=.west:=
   ((of_decide_eq_true row).resolve_left (fun h=>h floor)).resolve_left unblocked
 have sameHoles:=FirstFill13711.no_fill_before137_moves cut.before.logged stationary
 rcases direction with east|west
 · have checked : step soko1_1.board cut.middle .east=some cut.actor:=by simpa only [east] using cut.headChecked
   have shape:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 137 .east=[138] by decide +kernel) (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
   exact ⟨cut,metadata,east,shape,stationary,sameHoles⟩
 · have checked : step soko1_1.board cut.middle .west=some cut.actor:=by simpa only [west] using cut.headChecked
   have shape:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 137 .west=[136] by decide +kernel) (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 137 (.stay 136)):=by simpa only [shape] using cut.headEffect
   have outcomesEq:=cut.outcomesEq
   rw [shape] at outcomesEq
   have upperBound : energy soko1_1.initial final UpperBudget11.U6 (cut.beforeOutcomes++.push 137 (.stay 136)::cut.afterOutcomes)≤8 := by rw [←outcomesEq];exact upperCap
   have restBound : energy soko1_1.initial final UpperBudget11.Rest (cut.beforeOutcomes++.push 137 (.stay 136)::cut.afterOutcomes)≤4 := by rw [←outcomesEq];exact restCap
   exact False.elim (Row13313513711.canonical_no_west_with closure cut.before.logged checked effect cut.after completed stationary upperBound restBound)
#print axioms chronological_with
end Owner1007.StrongFirst137East11
