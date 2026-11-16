import Owner1007.PairFirstCut11
import Owner1007.UpperHeadCases11
namespace Owner1007.PairHeadCases11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.PairFirstCut11
def HeadCases (dir : Dir) (source : Option Cell) (outcome : Outcome) : Prop :=
 (dir=.east ∧ source=some 139 ∧ outcome=.push 139 (.stay 140)) ∨
 (dir=.east ∧ source=some 191 ∧ outcome=.push 191 (.stay 192)) ∨
 (dir=.east ∧ source=some 190 ∧ outcome=.push 190 (.stay 191)) ∨
 (dir=.west ∧ source=some 190 ∧ outcome=.push 190 (.stay 189)) ∨
 (dir=.east ∧ source=some 138 ∧ outcome=.push 138 (.stay 139)) ∨
 (dir=.west ∧ source=some 138 ∧ outcome=.push 138 (.stay 137)) ∨
 (dir=.east ∧ source=some 112 ∧ outcome=.push 112 (.stay 113)) ∨
 (dir=.east ∧ source=some 216 ∧ outcome=.push 216 (.stay 217))
theorem head_cases {dirs final pushes moves outcomes}
 (cut : UpperFirstCut11.FirstCut PairPath11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes) :
 HeadCases cut.direction cut.actor.pushSource cut.headOutcome := by
 obtain ⟨source,_,metadata,pays⟩ := cut.headPaid
 have holesInside := cut.before.logged.trace.holes_sublist.subset
 rcases pays with ⟨rfl,directionEq⟩|⟨rfl,directionEq⟩|⟨rfl,dirs⟩|⟨rfl,dirs⟩|⟨rfl,directionEq⟩|⟨rfl,directionEq⟩
 · have target : pushTargets soko1_1.board 139 cut.direction=[140] := by rw [directionEq]; decide +kernel
   have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
   exact Or.inl ⟨directionEq,metadata,head⟩
 · have target : pushTargets soko1_1.board 191 cut.direction=[192] := by rw [directionEq]; decide +kernel
   have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
   exact Or.inr (Or.inl ⟨directionEq,metadata,head⟩)
 · rcases dirs with directionEq|directionEq
   · have target : pushTargets soko1_1.board 190 cut.direction=[191] := by rw [directionEq]; decide +kernel
     have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
     exact Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩))
   · have target : pushTargets soko1_1.board 190 cut.direction=[189] := by rw [directionEq]; decide +kernel
     have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
     exact Or.inr (Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩)))
 · rcases dirs with directionEq|directionEq
   · have target : pushTargets soko1_1.board 138 cut.direction=[139] := by rw [directionEq]; decide +kernel
     have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
     exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩))))
   · have target : pushTargets soko1_1.board 138 cut.direction=[137] := by rw [directionEq]; decide +kernel
     have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
     exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩)))))
 · have target : pushTargets soko1_1.board 112 cut.direction=[113] := by rw [directionEq]; decide +kernel
   have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
   exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩))))))
 · have target : pushTargets soko1_1.board 216 cut.direction=[217] := by rw [directionEq]; decide +kernel
   have head := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
   exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨directionEq,metadata,head⟩)))))))

#print axioms head_cases
end Owner1007.PairHeadCases11
