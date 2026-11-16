import Owner1007.BlockRestNorth11
import Owner1007.Pure212Above11
import Owner1007.Left188Pocket11
import Owner1007.SmallRestTopColor11
namespace Owner1007.Left239BeforeRest11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def locks (_ : Fin 1) : List Cell := [239]
def region (_ : Fin 1) : List Cell := Pure212Above11.region 1
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region (fun _ _=>True) := by
 constructor
 ·intro i hero member dir target adjacent isFloor door notLock corner
  exact Pure212Above11.closed.1 1 hero member dir target adjacent isFloor door notLock corner
 ·intro i hero member dir source owner adjacent
  exact Or.inr (Or.inl trivial)
theorem head_south : Left188Pocket11.headCheck locks region 239 (fun d=>d=.south) 0=true := by decide +kernel

theorem impossible
 {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (cheap : pushes+lastPushes<335)
 (rest : energy soko1_1.initial final UpperBudget11.Rest (outcomes++last)<2)
 (cheap212 : energy soko1_1.initial final [212] (outcomes++last)<4)
 (noRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest dirs outcomes=0)
 (tag : endGroup [212] outcomes=[239]) (hero : state.player∈Pure212Above11.region 1) : False := by
 let full:=first.append suffix
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have selected:=first.end_subset (by decide) [212] (by decide) (by decide)
 have present239 : 239∈state.boulders:=selected.2 (by rw [tag];simp)
 have physical : [239]⊆state.boulders:=by simpa using present239
 have goneOriginal:=TightSurvivors11.singleton_nil full completed [212] (by decide) (by decide) (by decide)
   4 (by omega) 212 (by decide) (by decide +kernel)
 have gone : endGroup [239] last=[]:=by
  rw [endGroup_append,tag] at goneOriginal
  exact goneOriginal
 rcases first_cut_or_quiet (paid:=fun _ _=>True) suffix [239] with found|quiet
 ·obtain ⟨cut⟩:=found
  have zero:=QuietGroupFixed11.whole_fixed cut.before (by intro c h d;trivial)
  have beforeTag:=no_push_unchanged [239] cut.beforeOutcomes zero
  have good : OwnedCorral11.Good locks region state [239]:=⟨0,hero,List.Subset.refl _⟩
  obtain ⟨j,heroBefore,retained⟩:=Upper216Eight11.quiet_good_any closed (by intro i;change ([239]:List Cell).Nodup;decide)
    cut.before valid.1 (by decide) physical good first.trace.holes_sublist.subset
  have beforeFacts:=cut.before.logged.end_subset valid.1 [239] (by decide) physical
  obtain ⟨source,owner,metadata,_⟩:=cut.headPaid
  have source239 : source=239:=by rw [beforeTag] at owner;exact List.mem_singleton.mp owner
  subst source
  have beforePhysical : locks 0⊆cut.middle.boulders:=List.Subset.trans retained beforeFacts.2
  have south:=Left188Pocket11.head_allowed locks region 239 (fun d=>d=.south) 0 head_south
    cut.headChecked metadata heroBefore (step_player_clear _ _ _ _ cut.headChecked).1 beforePhysical
  have checked : step soko1_1.board cut.middle .south=some cut.actor:=by simpa only [south] using cut.headChecked
  let current:=first.append cut.before.logged
  have headEq:=UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
    (show pushTargets soko1_1.board 239 .south=[265] by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push 239 (.stay 265)):=by simpa only [headEq] using cut.headEffect
  let one : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome]:=
    .cons cut.headChecked cut.headEffect (.nil _)
  let next:=current.append one
  have localNoRest:=BlockRestNorth11.count_zero cut.before.logged 239 (Or.inr rfl) present239 zero
    (endGroup UpperBudget11.Rest outcomes)
  have beforeNoRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest
      (dirs++cut.beforeDirs) (outcomes++cut.beforeOutcomes)=0:=by
   rw [PaidCount11.append first,noRest,localNoRest]
  have nextNoRest : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest
      ((dirs++cut.beforeDirs)++[cut.direction]) ((outcomes++cut.beforeOutcomes)++[cut.headOutcome])=0:=by
   rw [PaidCount11.append current]
   simp [PaidCount11.count,PaidCount11.owned,FirstRest18711.paid,headEq,beforeNoRest]
  have wholeEq : (((outcomes++cut.beforeOutcomes)++[cut.headOutcome])++cut.afterOutcomes)=outcomes++last:=by
   calc
    _=outcomes++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes):=by simp only [List.append_assoc,List.singleton_append]
    _=outcomes++last:=congrArg (fun rest=>outcomes++rest) cut.outcomesEq.symm
  have nextRest : energy soko1_1.initial final UpperBudget11.Rest
      (((outcomes++cut.beforeOutcomes)++[cut.headOutcome])++cut.afterOutcomes)<2:=by rw [wholeEq];exact rest
  have nextCheap : pushes+cut.beforePushes+cut.actor.pushCost+cut.afterPushes<335:=by
   have counts:=cut.pushesEq
   omega
  have colors:=SmallRestTopColor11.prefix_colored next cut.after completed nextCheap nextRest nextNoRest
  have nextTag : endGroup [212] ((outcomes++cut.beforeOutcomes)++[cut.headOutcome])=[265]:=by
   rw [endGroup_append,endGroup_append,tag,beforeTag]
   change update [239] cut.headOutcome=[265]
   rw [headEq]
   decide
  have included:=end_subset_selected next (by decide) [212] Gate265Transport11.upperOrigins
    (by decide) (by decide) (by decide) (by decide)
  have bad : (265:Cell)∈Gate265Transport11.upper:=colors (included (by rw [nextTag];simp))
  exact (by decide : (265:Cell)∉Gate265Transport11.upper) bad
 ·have zero:=QuietGroupFixed11.whole_fixed quiet (by intro c h d;trivial)
  have fixed:=no_push_unchanged [239] last zero
  rw [fixed] at gone
  contradiction
#print axioms closed
#print axioms impossible
end Owner1007.Left239BeforeRest11
