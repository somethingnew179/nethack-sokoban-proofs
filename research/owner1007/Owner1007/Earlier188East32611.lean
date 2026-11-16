import Owner1007.Pair186188Word32611
namespace Owner1007.Earlier188East32611
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem before_west190 {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 190 (.stay 189)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after)
 (completed : Goal final) (cheap : beforePushes+t.pushCost+afterPushes≤326)
 (zero186 : energy soko1_1.initial final [186] (before++.push 190 (.stay 189)::after)=0) :
 Nonempty (FirstCut Pair186188Word32611.exit soko1_1.initial [188] beforeDirs state beforePushes beforeMoves before) := by
 rcases first_cut_or_quiet (paid:=Pair186188Word32611.exit) first [188] with found|quiet
 ·exact found
 ·let suffix := Logged.cons head effect last
  have cheapPrefix : beforePushes+(t.pushCost+afterPushes)≤326 := by omega
  obtain ⟨i,leftTag,rightTag⟩ := Pair186188Word32611.prefix_word first suffix completed cheapPrefix zero186 quiet
  have selected := first.end_subset (by decide) [188] (by decide) (by decide)
  rcases Pair186188Word32611.right_cases i with is188|is189
  ·have tag : endGroup [188] before=[188] := by simpa only [is188] using rightTag
   have present : 188∈state.boulders := selected.2 (by rw [tag];simp)
   let one : Logged soko1_1.board state [.west] t.state t.pushCost 1 [.push 190 (.stay 189)] :=
     .cons head effect (.nil _)
   let extended := first.append one
   have inside : TightRowPairs11.pairs 2⊆t.state.boulders := by
    change ([188,189] : List Cell)⊆t.state.boulders
    rw [effect.2]
    intro c member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :188≠190)).mpr present)
    ·simp
   exact False.elim (TightRowPairs32611.excluded extended last completed cheap 2 inside)
  ·have tag : endGroup [188] before=[189] := by simpa only [is189] using rightTag
   have present : 189∈state.boulders := selected.2 (by rw [tag];simp)
   have stateUnique := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1
   have nextUnique := step_boulders_nodup _ _ _ _ stateUnique head
   rw [effect.2] at nextUnique
   have fresh := (List.nodup_cons.mp nextUnique).1
   exact False.elim (fresh ((List.mem_erase_of_ne (by decide :189≠190)).mpr present))

theorem head_shape {dirs state pushes moves outcomes}
 (cut : FirstCut Pair186188Word32611.exit soko1_1.initial [188] dirs state pushes moves outcomes) :
 cut.actor.pushSource=some 189 ∧cut.direction=.east ∧cut.headOutcome=.push 189 (.stay 190) := by
 obtain ⟨source,owner,metadata,same,east⟩ := cut.headPaid
 subst source
 have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata
   (show pushTargets soko1_1.board 189 cut.direction=[190] by rw [east];decide +kernel)
   (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
 exact ⟨metadata,east,headEq⟩
#print axioms before_west190
#print axioms head_shape
end Owner1007.Earlier188East32611
