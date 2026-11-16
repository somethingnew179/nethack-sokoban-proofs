import Owner1007.Row19019111
import Owner1007.StrongShaftGate11
import Owner1007.Spare315Rest11
namespace Owner1007.Row190191Rest11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11 Owner1007.Row19019111
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem excluded {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (tail : Logged soko1_1.board state dirs final pushes moves outcomes)
 (completed : Goal final)
 (upperCap : energy soko1_1.initial final U6 (before++outcomes)≤8)
 (restCap : energy soko1_1.initial final Rest (before++outcomes)<2)
 (fixed137 : ownPushes [137] before=0) (fixed139 : ownPushes [139] before=0)
 (inside : [190,191]⊆state.boulders) (hero : state.player∈region 0) : False := by
 let full := first.append tail
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have tag137 := no_push_unchanged [137] before fixed137
 have tag139 := no_push_unchanged [139] before fixed139
 have physical137 : 137∈state.boulders := (first.end_subset (by decide) [137] (by decide) (by decide)).2 (by rw [tag137];simp)
 have physical139 : 139∈state.boulders := (first.end_subset (by decide) [139] (by decide) (by decide)).2 (by rw [tag139];simp)
 have selectedInside : ([190,191]++[137,139] : List Cell)⊆state.boulders := by
  apply List.append_subset.mpr
  refine ⟨inside,?_⟩
  intro c member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  ·exact physical137
  ·exact physical139
 have good : OwnedCorral11.Good locks region state [190,191] := ⟨0,hero,List.Subset.refl _⟩
 have hasCut : Nonempty (FirstCut paid state [190,191] dirs final pushes moves outcomes) := by
  rcases first_cut_or_quiet (paid:=paid) tail [190,191] with found|quiet
  ·exact found
  ·have lastGood := PairFirstCut11.quiet_good closed unique (by intro i;rfl) quiet valid.1
      (by decide) inside (by decide) good first.trace.holes_sublist.subset
   obtain ⟨i,_,retained⟩ := lastGood
   have selected := (tail.end_subset valid.1 [190,191] (by decide) inside).2
   have physical : ([190,191] : List Cell)⊆final.boulders := List.Subset.trans retained selected
   have cap := Spare315Rest11.other_capacity full completed restCap [190,191] (by decide) physical (by decide)
   change 2≤1 at cap
   omega
 obtain ⟨cut⟩ := hasCut
 have sep : GrowingCorral11.Separated locks region state [190,191] [137,139] :=
   ⟨0,hero,List.Subset.refl _,outside⟩
 have noGate := (GrowingCorral11.Quiet.separated_untouched closed unique growth cut.before valid.1
   (by decide) selectedInside sep first.trace.holes_sublist.subset).2
 have local137 := LeftQuietIdentity11.subset_zero [137] [137,139] cut.beforeOutcomes (by decide) noGate
 have local139 := LeftQuietIdentity11.subset_zero [139] [137,139] cut.beforeOutcomes (by decide) noGate
 have whole137 : ownPushes [137] (before++cut.beforeOutcomes)=0 := by rw [ownPushes_append,tag137,fixed137,local137]
 have whole139 : ownPushes [139] (before++cut.beforeOutcomes)=0 := by rw [ownPushes_append,tag139,fixed139,local139]
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 rcases pays with ⟨rfl,north⟩
 let current := first.append cut.before.logged
 have checked : step soko1_1.board cut.middle .north=some cut.actor := by simpa only [north] using cut.headChecked
 have headEq := UpperHeadCases11.ordinary_effect checked cut.headEffect metadata
   (show pushTargets soko1_1.board 190 .north=[164] from by decide +kernel) (by decide +kernel) current.trace.holes_sublist.subset
 have effect : Matches cut.middle cut.actor (.push 190 (.stay 164)) := by simpa only [headEq] using cut.headEffect
 have eqEffects : (before++cut.beforeOutcomes)++.push 190 (.stay 164)::cut.afterOutcomes=before++outcomes := by
  calc
   _=before++(cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes) := by rw [headEq];simp only [List.append_assoc]
   _=before++outcomes := congrArg (fun middle=>before++middle) cut.outcomesEq.symm
 have upperCheap : energy soko1_1.initial final U6 ((before++cut.beforeOutcomes)++.push 190 (.stay 164)::cut.afterOutcomes)≤8 := by rw [eqEffects];exact upperCap
 have restCheap : energy soko1_1.initial final Rest ((before++cut.beforeOutcomes)++.push 190 (.stay 164)::cut.afterOutcomes)≤4 := by rw [eqEffects];omega
 rcases StrongShaftGate11.gate_moved_before_north current checked effect cut.after completed upperCheap restCheap with moved|moved
 ·omega
 ·omega

#print axioms excluded
end Owner1007.Row190191Rest11
