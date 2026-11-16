import Owner1007.NoTopDown265Before18711
namespace Owner1007.TopBefore187Split11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem split {dirs state pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (prefixLog : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last)
 (completed : Goal final) (cheap : pushes+lastPushes≤325)
 (noNorth : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest dirs outcomes=0)
 (group : List Cell) (groupUnique : group.Nodup) (subset : group⊆Gate265Transport11.upperOrigins) :
 UpperQuiet11.Quiet Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs state pushes moves outcomes ∨
 ∃cut : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs state pushes moves outcomes,
   ownPushes (endGroup group cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=0 := by
 let logged := prefixLog.append suffix
 have zeroRest := (Tight32511.budgets logged completed cheap).2.2.2
 rcases first_cut_or_quiet (paid:=Gate265Transport11.paid) prefixLog soko1_1.initial.boulders with found|quiet
 ·obtain ⟨cut⟩ := found
  let globalCut := TransportEvents11.FirstCut.extend cut suffix
  obtain ⟨source,sourceRest,metadata,shape⟩ := Gate265FirstBelow11.below logged completed cheap globalCut
  change source∈endGroup UpperBudget11.Rest cut.beforeOutcomes at sourceRest
  change cut.actor.pushSource=some source at metadata
  change (source=264∧cut.direction=.east)∨(source=266∧cut.direction=.west)∨(source=291∧cut.direction=.north) at shape
  have target : pushTargets soko1_1.board source cut.direction=[265] := by
   rcases shape with ⟨rfl,east⟩|⟨rfl,west⟩|⟨rfl,north⟩
   ·rw [east];decide +kernel
   ·rw [west];decide +kernel
   ·rw [north];decide +kernel
  have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target
    (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
  have effect : Matches cut.middle cut.actor (.push source (.stay 265)) := by simpa only [headEq] using cut.headEffect
  let top := endGroup group cut.beforeOutcomes
  have initialInside : group⊆soko1_1.initial.boulders := List.Subset.trans subset (by decide)
  have included := end_subset_selected cut.before.logged (by decide) group Gate265Transport11.upperOrigins
    groupUnique (by decide) subset (by decide)
  have topColored : top⊆Gate265Transport11.upper := List.Subset.trans included (Gate265Transport11.quiet_upper cut.before)
  have topSelected := cut.before.logged.end_subset (by decide) group groupUnique initialInside
  have sourceOutside : source∉Gate265Transport11.upper := by
   rcases shape with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> decide +kernel
  have sourceNotTop : source∉top := fun h=>sourceOutside (topColored h)
  have topSame : update top cut.headOutcome=top := by
   rw [headEq]
   simp only [update,move,if_neg sourceNotTop]
  let headLog : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
    .cons cut.headChecked cut.headEffect (.nil _)
  let first := cut.before.logged.append headLog
  have frontRest : 265∈endGroup UpperBudget11.Rest (cut.beforeOutcomes++[cut.headOutcome]) := by
   rw [endGroup_append]
   change 265∈update (endGroup UpperBudget11.Rest cut.beforeOutcomes) cut.headOutcome
   rw [headEq]
   simp only [update,move,if_pos sourceRest,post]
   simp
  have headTopInside := GhostSubset.update_subset cut.middle cut.actor cut.headOutcome cut.headEffect top topSelected.1 topSelected.2
  rw [topSame] at headTopInside
  have frontActual : 265∈cut.actor.state.boulders := by rw [effect.2];simp
  have noFrontTop : 265∉top := fun h=>(show (265:Cell)∉Gate265Transport11.upper from by decide) (topColored h)
  have bothUnique : (([265] : List Cell)++top).Nodup := by
   change (265::top).Nodup
   exact List.nodup_cons.mpr ⟨noFrontTop,topSelected.1⟩
  have bothInside : ([265] : List Cell)++top⊆cut.actor.state.boulders := by
   intro c member
   rcases List.mem_cons.mp member with rfl|later
   ·exact frontActual
   ·exact headTopInside later
  have hero : cut.actor.state.player∈Gate265Transport11.lower := by
   have same : cut.actor.state.player=source := by rw [effect.2]
   rw [same]
   rcases shape with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> decide +kernel
  have outside : ∀c,c∈top→c∉Gate265Transport11.lower := fun c h=>NoTopDown265Before18711.upper_outside_lower c (topColored h)
  have concatNoNorth : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest
      (cut.beforeDirs++cut.direction::cut.afterDirs) (cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)=0 := by
   simpa only [←cut.dirsEq,←cut.outcomesEq] using noNorth
  rw [PaidCount11.append cut.before.logged] at concatNoNorth
  change PaidCount11.count FirstRest18711.paid UpperBudget11.Rest cut.beforeDirs cut.beforeOutcomes+
    ((if PaidCount11.owned FirstRest18711.paid (endGroup UpperBudget11.Rest cut.beforeOutcomes) cut.direction cut.headOutcome then 1 else 0)+
     PaidCount11.count FirstRest18711.paid (update (endGroup UpperBudget11.Rest cut.beforeOutcomes) cut.headOutcome) cut.afterDirs cut.afterOutcomes)=0 at concatNoNorth
  have afterNoNorth : PaidCount11.count FirstRest18711.paid
      (endGroup UpperBudget11.Rest (cut.beforeOutcomes++[cut.headOutcome])) cut.afterDirs cut.afterOutcomes=0 := by
   rw [endGroup_append]
   change PaidCount11.count FirstRest18711.paid (update (endGroup UpperBudget11.Rest cut.beforeOutcomes) cut.headOutcome) cut.afterDirs cut.afterOutcomes=0
   omega
  have zeroForFront : energy soko1_1.initial final UpperBudget11.Rest
      ((cut.beforeOutcomes++[cut.headOutcome])++cut.afterOutcomes++last)=0 := by
   have eqEffects : (cut.beforeOutcomes++[cut.headOutcome])++cut.afterOutcomes++last=outcomes++last := by
    calc
     _=(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)++last := by simp only [List.append_assoc,List.singleton_append]
     _=outcomes++last := congrArg (fun middle=>middle++last) cut.outcomesEq.symm
   rw [eqEffects]
   exact zeroRest
  have untouched := Front26511.top_untouched first cut.after suffix zeroForFront frontRest afterNoNorth top bothUnique bothInside hero outside
  have headZero : ownPush top cut.headOutcome=0 := by
   rw [headEq]
   simp only [ownPush,if_neg sourceNotTop]
  have wholeZero : ownPushes top (cut.headOutcome::cut.afterOutcomes)=0 := by
   simpa only [ownPushes,headZero,topSame,Nat.zero_add] using untouched
  exact Or.inr ⟨cut,wholeZero⟩
 ·exact Or.inl quiet

#print axioms split
end Owner1007.TopBefore187Split11
