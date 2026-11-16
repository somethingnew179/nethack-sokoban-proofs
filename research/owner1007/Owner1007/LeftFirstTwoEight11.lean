import Owner1007.LeftFirstTwo11
import Owner1007.LeftSplitEight11
namespace Owner1007.LeftFirstTwoEight11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11 Owner1007.LeftFirstTwo11
theorem eight_of_other_second {state final : State}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (cut : FirstCut LeftPair11.paid state (endGroup [186,212] before) dirs final pushes moves outcomes)
 (completed : Goal final)
 (i : Fin 2) (same : (endGroup [186,212] before).Perm (LeftPair11.locks i))
 (hero : state.player∈LeftPair11.region i)
 (sourceEq : cut.actor.pushSource=some (otherSource i))
 (cashFirst : 1≤PaidCount11.count LeftPair11.paid [186,212] beforeDirs before) :
 8≤energy soko1_1.initial final [186,212] (before++outcomes) := by
 have facts := first.end_subset (by decide) [186,212] (by decide) (by decide)
 have bounded := endGroup_length_le [186,212] before
 change (endGroup [186,212] before).length≤2 at bounded
 obtain ⟨frame,heroAfter⟩ := other_head cut first.trace facts.1 facts.2 bounded i same hero sourceEq
 let headLogged : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
   .cons cut.headChecked cut.headEffect (.nil _)
 let between := cut.before.logged.append headLogged
 let prefixLogged := first.append between
 have prefixFrame : (endGroup [186,212] (before++(cut.beforeOutcomes++[cut.headOutcome]))).Perm [185,211] := by
   rw [endGroup_append,endGroup_append]
   exact frame
 have event := PaidCount11.event_le (lastDirs:=[]) (last:=[]) cut.before.logged cut.headEffect
   (endGroup [186,212] before) cut.headPaid
 have secondCash : 1≤PaidCount11.count LeftPair11.paid (endGroup [186,212] before)
     (cut.beforeDirs++[cut.direction]) (cut.beforeOutcomes++[cut.headOutcome]) := by
   simpa only [PaidCount11.count,Nat.add_zero] using event
 have appendCount := PaidCount11.append first LeftPair11.paid [186,212]
   (cut.beforeDirs++[cut.direction]) (cut.beforeOutcomes++[cut.headOutcome])
 have cash : 2≤PaidCount11.count LeftPair11.paid [186,212]
     (beforeDirs++(cut.beforeDirs++[cut.direction])) (before++(cut.beforeOutcomes++[cut.headOutcome])) := by omega
 have bound := LeftSplitEight11.eight_of_split prefixLogged cut.after completed prefixFrame heroAfter cash
 have shape : (before++(cut.beforeOutcomes++[cut.headOutcome]))++cut.afterOutcomes=before++outcomes := by
   calc
     _ = before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes) := by
       simp only [List.append_assoc,List.singleton_append]
     _ = before++outcomes := congrArg (List.append before) cut.outcomesEq.symm
 simpa only [shape] using bound
#print axioms eight_of_other_second
end Owner1007.LeftFirstTwoEight11
