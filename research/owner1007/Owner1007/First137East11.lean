import Owner1007.FirstFill13711
import Owner1007.First137RestAnywhere11
import Owner1007.WestRankHead11
import Owner1007.QuietFixed11

namespace Owner1007.First137East11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def paid (_ : Cell) (_ : Dir) : Prop := True
instance (c : Cell) (d : Dir) : Decidable (paid c d) := by unfold paid;infer_instance
def headCheck : Bool:=allDirs.all fun dir=>match advance soko1_1.board 137 dir.opposite with
 |none=>true
 |some hero=>decide (hero∉soko1_1.board.floor ∨ BlockedPush soko1_1.board [] 137 dir ∨ dir=.east ∨ dir=.west)
theorem head_checked : headCheck=true:=by decide +kernel

theorem chronological {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (restZero : energy soko1_1.initial final UpperBudget11.Rest outcomes=0) :
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
   have price:=First137RestAnywhere11.rest_two cut.before.logged checked effect cut.after completed stationary
   have outcomesEq:=cut.outcomesEq
   rw [shape] at outcomesEq
   rw [←outcomesEq] at price
   omega
#print axioms chronological
end Owner1007.First137East11

