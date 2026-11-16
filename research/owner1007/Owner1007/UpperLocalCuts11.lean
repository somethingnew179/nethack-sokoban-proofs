import Owner1007.WestRankHead11
import Owner1007.UpperHeadCases11
namespace Owner1007.UpperLocalCuts11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem first_cut {state final : State} {history dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state beforePushes beforeMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤3)
 (good : OwnedCorral11.Good UpperZero11.locks UpperZero11.region state group) :
 Nonempty (UpperFirstCut11.FirstCut UpperZero11.paid state group dirs final pushes moves outcomes) := by
 rcases UpperFirstCut11.first_cut_or_quiet logged group with found|quiet
 · exact found
 · have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   have finalGood := PairFirstCut11.quiet_good UpperZero11.closed UpperZero11.unique UpperZero11.size quiet
     valid.1 groupUnique inside bounded good reached.holes_sublist.subset
   obtain ⟨i,_,selected⟩ := finalGood
   have actual := (logged.end_subset valid.1 group groupUnique inside).2
   have card := List.Nodup.length_le_of_subset (UpperZero11.unique i) (List.Subset.trans selected actual)
   rw [UpperZero11.size i] at card
   have conservation := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   rw [empty] at conservation
   change 18+0=final.boulders.length+16 at conservation
   omega
theorem head_cases {state group dirs final pushes moves outcomes history past pastMoves}
    (cut : FirstCut UpperZero11.paid state group dirs final pushes moves outcomes)
    (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves) :
    UpperHeadCases11.HeadCases cut.direction cut.actor.pushSource cut.headOutcome := by
  obtain ⟨source,_,metadata,paid⟩ := cut.headPaid
  have holesInside := (reached.append cut.before.logged.trace).holes_sublist.subset
  rcases paid with ⟨rfl,directionEq⟩ | ⟨rfl,directionEq⟩ | ⟨rfl,directionEq⟩ | ⟨rfl,dirs⟩ | ⟨rfl,dirs⟩ | ⟨rfl,directionEq⟩
  · have target : pushTargets soko1_1.board 137 cut.direction=[136] := by rw [directionEq]; decide +kernel
    have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
    exact Or.inl ⟨directionEq,metadata,head⟩
  · have target : pushTargets soko1_1.board 139 cut.direction=[140] := by rw [directionEq]; decide +kernel
    have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
    exact Or.inr (Or.inl ⟨directionEq,metadata,head⟩)
  · have target : pushTargets soko1_1.board 191 cut.direction=[192] := by rw [directionEq]; decide +kernel
    have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
    exact Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩))
  · rcases dirs with directionEq|directionEq
    · have target : pushTargets soko1_1.board 138 cut.direction=[139] := by rw [directionEq]; decide +kernel
      have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩)))
    · have target : pushTargets soko1_1.board 138 cut.direction=[137] := by rw [directionEq]; decide +kernel
      have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩))))
  · rcases dirs with directionEq|directionEq
    · have target : pushTargets soko1_1.board 190 cut.direction=[191] := by rw [directionEq]; decide +kernel
      have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩)))))
    · have target : pushTargets soko1_1.board 190 cut.direction=[189] := by rw [directionEq]; decide +kernel
      have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩))))))
  · have target : pushTargets soko1_1.board 216 cut.direction=[217] := by rw [directionEq]; decide +kernel
    have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨directionEq,metadata,head⟩)))))))
#print axioms first_cut
#print axioms head_cases
end Owner1007.UpperLocalCuts11
