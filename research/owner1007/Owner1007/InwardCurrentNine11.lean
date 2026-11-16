import Owner1007.CorralQuietCell11
import Owner1007.RightPocketNine11
namespace Owner1007.InwardCurrentNine11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11 Owner1007.UpperBudget11
open Owner1007.Inward191Eight11 (locks region paid)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The inward gate reserves nine with current owned193, even if the
original191 has already moved and returned. No original-history premise. -/
theorem reserve_nine {state final : State}
 {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (good : OwnedCorral11.Good locks region state (endGroup U6 before))
 (owns193 : (193:Cell)∈endGroup U6 before) :
 9≤energy soko1_1.initial final U6 (before++outcomes) := by
 let logged := first.append last
 by_cases enough : 9≤energy soko1_1.initial final U6 (before++outcomes)
 · exact enough
 · have cheap : energy soko1_1.initial final U6 (before++outcomes)≤8 := by omega
   have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
   have facts := first.end_subset (by decide) U6 (by decide) (by decide)
   have wholeGone := Budget32711.upper_gone logged completed cheap
   have gone : endGroup (endGroup U6 before) outcomes=[] := by rw [←endGroup_append];exact wholeGone
   obtain ⟨cut⟩ := Upper216Eight11.first_any Inward191Eight11.closed Inward191Eight11.unique
     Inward191Eight11.nonempty last valid.1 facts.1 facts.2 good first.trace.holes_sublist.subset gone
   obtain ⟨i,heroBefore,locksBefore⟩ := Upper216Eight11.quiet_good_any Inward191Eight11.closed Inward191Eight11.unique
     cut.before valid.1 facts.1 facts.2 good first.trace.holes_sublist.subset
   have beforeFacts := cut.before.logged.end_subset valid.1 (endGroup U6 before) facts.1 facts.2
   have physicalBefore := List.Subset.trans locksBefore beforeFacts.2
   obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
   obtain ⟨rfl,south⟩ := Inward191Eight11.head_shape i heroBefore physicalBefore pays cut.headChecked metadata
   have checked : step soko1_1.board cut.middle .south=some cut.actor := by simpa only [south] using cut.headChecked
   have currentFirst := first.append cut.before.logged
   have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
     (show pushTargets soko1_1.board 190 .south=[216] by decide +kernel) (by decide +kernel)
     currentFirst.trace.holes_sublist.subset
   have effect : Matches cut.middle cut.actor (.push 190 (.stay 216)) := by simpa only [headEq] using cut.headEffect
   have zero193 := CorralQuietCell11.inward193_zero cut.before valid.1 facts.1 facts.2 good first.trace.holes_sublist.subset
   have tag193 := no_push_unchanged [193] cut.beforeOutcomes zero193
   have singleSubset : [193]⊆endGroup U6 before := by simpa using owns193
   have mono := cut.before.logged.end_mono valid.1 [193] (endGroup U6 before) (by decide)
     (List.Subset.trans singleSubset facts.2) singleSubset
   rw [tag193] at mono
   have selectedBefore : ([190,191,193]:List Cell)⊆endGroup (endGroup U6 before) cut.beforeOutcomes := by
     intro c found
     simp only [List.mem_cons,List.not_mem_nil,or_false] at found
     rcases found with rfl|rfl|rfl
     · exact owner
     · exact locksBefore (Inward191Eight11.has191 i)
     · exact mono (by simp)
   have afterSelected := update_mono [190,191,193] (endGroup (endGroup U6 before) cut.beforeOutcomes)
     (by decide) selectedBefore cut.headOutcome
   rw [headEq] at afterSelected
   have selected : RightTripleEight11.locks 0⊆
       endGroup U6 ((before++cut.beforeOutcomes)++[.push 190 (.stay 216)]) := by
     rw [endGroup_append,endGroup_append]
     change RightTripleEight11.locks 0⊆update (endGroup (endGroup U6 before) cut.beforeOutcomes) (.push 190 (.stay 216))
     exact List.Subset.trans (by decide +kernel) afterSelected
   let headLogged : Logged soko1_1.board cut.middle [.south] cut.actor.state cut.actor.pushCost 1 [.push 190 (.stay 216)] :=
     .cons checked effect (.nil _)
   let extended := currentFirst.append headLogged
   have hero : cut.actor.state.player∈RightTripleEight11.region 0 := by
     have same : cut.actor.state.player=190 := by rw [effect.2]
     rw [same]
     exact Gate191216Eight11.hero190
   have bound := RightPocketNine11.reserve_nine extended cut.after completed hero selected
   have allEffects : ((before++cut.beforeOutcomes)++[.push 190 (.stay 216)])++cut.afterOutcomes=before++outcomes := by
     calc
       _ = (before++cut.beforeOutcomes)++.push 190 (.stay 216)::cut.afterOutcomes := by simp only [List.append_assoc,List.singleton_append]
       _ = before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes) := by rw [headEq];simp only [List.append_assoc]
       _ = before++outcomes := congrArg (List.append before) cut.outcomesEq.symm
   rw [allEffects] at bound
   omega
#print axioms reserve_nine
end Owner1007.InwardCurrentNine11
