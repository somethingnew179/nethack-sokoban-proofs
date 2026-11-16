import Owner1007.UpperNoFrozen11
import Owner1007.QuietFixed11
import Owner1007.Gate265Markers11
namespace Owner1007.Mate141Before13911
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperBudget11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def directionCheck : Bool := allDirs.all fun dir=>
 match advance soko1_1.board 141 dir.opposite with
 | none=>true
 | some hero=>decide (hero∉soko1_1.board.floor∨BlockedPush soko1_1.board [] 141 dir∨dir=.east∨dir=.west)
theorem checked : directionCheck=true := by decide +kernel
theorem east_or_west {state dir t}
 (head : step soko1_1.board state dir=some t) (metadata : t.pushSource=some 141) : dir=.east∨dir=.west := by
 have hero := (step_player_clear _ _ _ _ head).1
 have reverse := Geometry.reverseCheck_sound soko1_1.board ZeroWord11.reverse_checked state.player hero dir 141
   (PairPost11.source_adjacent head metadata)
 have row := List.all_eq_true.mp checked dir (Geometry.all_directions dir)
 simp only [directionCheck,reverse] at row
 exact ((of_decide_eq_true row).resolve_left (fun h=>h hero)).resolve_left
   (WestRankHead11.source_unblocked head metadata (by simp : ([]:List Cell)⊆state.boulders))

/-- Before original139 moves, original141 cannot move either: West freezes
139/140 and East parks the selected stone at the dead142 square. -/
theorem stationary {state final : State}
 {dirs lastDirs : List Dir} {pushes moves lastPushes lastMoves : Nat} {outcomes last : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial dirs state pushes moves outcomes)
 (suffix : Logged soko1_1.board state lastDirs final lastPushes lastMoves last) (completed : Goal final)
 (cap : energy soko1_1.initial final U6 (outcomes++last)≤8)
 (fixed139 : ownPushes [139] outcomes=0) : ownPushes [141] outcomes=0 := by
 rcases first_cut_or_quiet (paid:=Gate265Markers11.firstPaid 141) first [141] with found|quiet
 · obtain ⟨cut⟩ := found
   have fixed141 := cut.before.fixed (by decide : 141∈([141]:List Cell)) (by intro dir;rfl)
   have before139 : ownPushes [139] cut.beforeOutcomes=0 := by
     rw [cut.outcomesEq,ownPushes_append] at fixed139
     omega
   have tag139 := no_push_unchanged [139] cut.beforeOutcomes before139
   have tag141 := no_push_unchanged [141] cut.beforeOutcomes fixed141
   have mono139 := cut.before.logged.end_mono (by decide) [139] U6 (by decide) (by decide) (by decide)
   have mono141 := cut.before.logged.end_mono (by decide) [141] U6 (by decide) (by decide) (by decide)
   rw [tag139] at mono139
   rw [tag141] at mono141
   have pairBefore : [139,141]⊆endGroup U6 cut.beforeOutcomes := by
     intro c member
     rcases List.mem_cons.mp member with rfl|later
     · exact mono139 (by simp)
     · have eq : c=141 := List.mem_singleton.mp later
       subst c
       exact mono141 (by simp)
   have transport := update_mono [139,141] (endGroup U6 cut.beforeOutcomes) (by decide) pairBefore cut.headOutcome
   obtain ⟨source,_,metadata,same⟩ := cut.headPaid
   change source=141 at same
   subst source
   let one : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
     .cons cut.headChecked cut.headEffect (.nil _)
   let headPrefix := cut.before.logged.append one
   let tail := cut.after.append suffix
   have wholeShape : (cut.beforeOutcomes++[cut.headOutcome])++(cut.afterOutcomes++last)=outcomes++last := by
     calc
       _ = (cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)++last := by simp only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]
       _ = outcomes++last := congrArg (fun word=>word++last) cut.outcomesEq.symm
   have headCap : energy soko1_1.initial final U6
       ((cut.beforeOutcomes++[cut.headOutcome])++(cut.afterOutcomes++last))≤8 := by rw [wholeShape];exact cap
   rcases east_or_west cut.headChecked metadata with east|west
   · have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata
       (by rw [east];change pushTargets soko1_1.board 141 .east=[142];decide +kernel)
       (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
     have selected : [142]⊆endGroup U6 (cut.beforeOutcomes++[cut.headOutcome]) := by
       rw [endGroup_append]
       change [142]⊆update (endGroup U6 cut.beforeOutcomes) cut.headOutcome
       rw [headEq] at transport ⊢
       exact List.Subset.trans (by decide) transport
     exact False.elim (UpperNoFrozen11.excluded headPrefix tail completed headCap [142]
       (locked_of_check _ [142] (by decide +kernel)) 142 (by simp) selected)
   · have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata
       (by rw [west];change pushTargets soko1_1.board 141 .west=[140];decide +kernel)
       (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
     have selected : [139,140]⊆endGroup U6 (cut.beforeOutcomes++[cut.headOutcome]) := by
       rw [endGroup_append]
       change [139,140]⊆update (endGroup U6 cut.beforeOutcomes) cut.headOutcome
       rw [headEq] at transport ⊢
       exact List.Subset.trans (by decide) transport
     exact False.elim (UpperNoFrozen11.excluded headPrefix tail completed headCap [139,140]
       (locked_of_check _ [139,140] (by decide +kernel)) 139 (by simp) selected)
 · exact quiet.fixed (by decide : 141∈([141]:List Cell)) (by intro dir;rfl)
#print axioms east_or_west
#print axioms stationary
end Owner1007.Mate141Before13911
