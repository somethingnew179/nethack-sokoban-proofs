import Owner1007.UpperResetHistory11
import Owner1007.Paid137Six11
import Owner1007.UpperSixBudget11
namespace Owner1007.UpperResetBudget11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def source (i : Fin 2) : Cell := if i.val=0 then 138 else 190
def landing (i : Fin 2) : Cell := if i.val=0 then 139 else 191
def support (i : Fin 2) : Cell := if i.val=0 then 137 else 189
def old (i : Fin 2) : List Cell := if i.val=0 then [138,191] else [139,190]
theorem edge : ∀ i, (support i,source i,landing i,Dir.east,old i,[139,191])∈PairPost11.edges := by
 intro i
 obtain ⟨v,h⟩ := i
 have choices : v=0∨v=1 := by omega
 rcases choices with rfl|rfl <;> simp [support,source,landing,old,PairPost11.edges]

theorem source_exit : ∀ i, CutActor11.Exit (source i) .east := by
 intro i
 unfold source
 split <;> simp [CutActor11.Exit]

theorem source_paid : ∀ i, PairPath11.paid (source i) .east := by decide +kernel
theorem source_hero : ∀ i, source i∈([138,190] : List Cell) := by decide +kernel

theorem pair_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (i : Fin 2) (sourceEq : cut.actor.pushSource=some (source i)) (directionEq : cut.direction=.east)
 (effect : Matches cut.middle cut.actor (.push (source i) (.stay (landing i))))
 (cheap137 : energy soko1_1.initial final [137] outcomes<2) :
 4≤energy soko1_1.initial final TightSplit11.A outcomes := by
 have exit : CutActor11.Exit (source i) cut.direction := by rw [directionEq]; exact source_exit i
 have owner := UpperResetHistory11.head_pair_owned cut sourceEq exit cheap137
 have pays : OwnedCorral11.PaidStep PairPath11.paid
     (endGroup PairFirstCut11.originalGroup cut.beforeOutcomes) cut.direction cut.actor :=
   ⟨source i,owner,sourceEq,by rw [directionEq]; exact source_paid i⟩
 let pairCut := UpperToPair11.as_pair cut pays
 have pairPerm := PairPost11.before_after (support:=support i) (source:=source i) (landing:=landing i)
   (dir:=.east) (old:=old i) (next:=[139,191]) pairCut (edge i) sourceEq directionEq effect
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
 have actual := step_boulders_nodup _ _ _ _ valid.1 cut.headChecked
 have before := cut.before.logged.end_subset (by decide) TightSplit11.A (by decide) (by decide)
 have insideAfter := GhostSubset.update_subset _ _ _ cut.headEffect _ before.1 before.2
 have reached := cut.before.logged.trace.append (Trace.cons cut.headChecked (Trace.nil cut.actor.state))
 have inside : [139,191]⊆cut.actor.state.boulders := by
   intro cell found
   exact insideAfter (pairPerm.2.mem_iff.mpr found)
 have hero : cut.actor.state.player∈([138,190] : List Cell) := by
   have same : cut.actor.state.player=source i := by rw [effect.2]
   rw [same]; exact source_hero i
 have active := Paid137Six11.active_after_stay pairCut effect
 have future := PairResetFuture11.future_two reached cut.after completed active hero inside
 have equal := Hero315Frame11.energy_perm pairPerm.2 cut.actor.state final cut.afterOutcomes
 have nextTwo : 2≤energy cut.actor.state final
     (update (endGroup TightSplit11.A cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes := by
   change energy cut.actor.state final (update (endGroup TightSplit11.A cut.beforeOutcomes) cut.headOutcome)
     cut.afterOutcomes=energy cut.actor.state final [139,191] cut.afterOutcomes at equal
   omega
 have row := CutStrict11.exit_row scalar rfl valid cut.headChecked cut.headEffect before.1 before.2
   ⟨source i,owner,sourceEq,exit⟩
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup TightSplit11.A cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup TightSplit11.A cut.beforeOutcomes) cut.headOutcome)-
   value cut.middle (endGroup TightSplit11.A cut.beforeOutcomes) at row
 have prefixNN := energy_nonnegative cut.before.logged TightSplit11.A (by decide) (by decide)
 have split := energy_append soko1_1.initial cut.middle final TightSplit11.A cut.beforeOutcomes
   (cut.headOutcome::cut.afterOutcomes)
 have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup TightSplit11.A cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup TightSplit11.A cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
   charge NetHack.Soko11Hero315.holeWeight (endGroup TightSplit11.A cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (update (endGroup TightSplit11.A cut.beforeOutcomes) cut.headOutcome)-
   value cut.middle (endGroup TightSplit11.A cut.beforeOutcomes)+
   energy cut.actor.state final (update (endGroup TightSplit11.A cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
 have same := congrArg (energy soko1_1.initial final TightSplit11.A) cut.outcomesEq
 omega
#print axioms pair_four

theorem cheap_c_two {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (i : Fin 2) (sourceEq : cut.actor.pushSource=some (source i)) (directionEq : cut.direction=.east)
 (effect : Matches cut.middle cut.actor (.push (source i) (.stay (landing i))))
 (cheap : energy soko1_1.initial final U6 outcomes<6) :
 ∀ cell∈C, energy soko1_1.initial final [cell] outcomes<2 := by
 have cheap137 : energy soko1_1.initial final [137] outcomes<2 := by
   by_cases enough : 2≤energy soko1_1.initial final [137] outcomes
   · have six := Paid137Six11.upper_six logged completed enough
     omega
   · omega
 have pair := pair_four logged completed cut i sourceEq directionEq effect cheap137
 have split := Hero315Frame11.energy_split logged TightSplit11.A C (by decide) (by decide)
 change energy soko1_1.initial final U6 outcomes=_ at split
 have all := c_sum logged
 have a := energy_nonnegative logged [137] (by decide) (by decide)
 have b := energy_nonnegative logged [141] (by decide) (by decide)
 have c := energy_nonnegative logged [188] (by decide) (by decide)
 have d := energy_nonnegative logged [193] (by decide) (by decide)
 intro cell member
 change cell∈[137,141,188,193] at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl <;> omega
#print axioms cheap_c_two
end Owner1007.UpperResetBudget11
