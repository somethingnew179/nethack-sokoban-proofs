import Owner1007.UpperFirstCut11
namespace Owner1007.UpperHeadCases11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.UpperFirstCut11

theorem ordinary_effect {state : State} {dir : Dir} {t : Transition} {outcome : Outcome} {source landing : Cell}
    (checked : step soko1_1.board state dir=some t) (effect : Matches state t outcome)
    (sourceEq : t.pushSource=some source) (targets : pushTargets soko1_1.board source dir=[landing])
    (notHole : landing∉soko1_1.initial.holes) (holesInside : state.holes⊆soko1_1.initial.holes) :
    outcome=.push source (.stay landing) := by
  rcases step_cases_full _ _ _ _ checked with walked|pushed
  · obtain ⟨target,_,_,_,_,shape⟩ := walked
    simp only [shape] at sourceEq
    contradiction
  · obtain ⟨other,result,_,_,present,push,shape⟩ := pushed
    have same : other=source := by simpa only [shape,Option.some.injEq] using sourceEq
    subst other
    have spec := pushBoulder_spec _ _ _ _ _ push
    have landingEq : result.landing=landing := by simpa only [targets,List.mem_singleton] using spec.2
    have unfilled : result.filled=none := by
      rcases spec.1 with stay|fill
      · exact stay.1
      · exact False.elim (notHole (holesInside (landingEq ▸ fill.2.1)))
    have boxes : result.boulders=landing::state.boulders.erase source := by
      rcases spec.1 with stay|fill
      · simpa only [landingEq] using stay.2
      · simp [unfilled] at fill
    have actualEffect : Matches state t (.push source (.stay landing)) := by
      refine ⟨present,?_⟩
      simpa only [unfilled,boxes,landingEq,afterFill] using shape
    exact GhostProjection.matches_unique state t outcome (.push source (.stay landing)) effect actualEffect

def HeadCases (dir : Dir) (source : Option Cell) (outcome : Outcome) : Prop :=
 (dir=.west ∧ source=some 137 ∧ outcome=.push 137 (.stay 136)) ∨
 (dir=.east ∧ source=some 139 ∧ outcome=.push 139 (.stay 140)) ∨
 (dir=.east ∧ source=some 191 ∧ outcome=.push 191 (.stay 192)) ∨
 (dir=.east ∧ source=some 138 ∧ outcome=.push 138 (.stay 139)) ∨
 (dir=.west ∧ source=some 138 ∧ outcome=.push 138 (.stay 137)) ∨
 (dir=.east ∧ source=some 190 ∧ outcome=.push 190 (.stay 191)) ∨
 (dir=.west ∧ source=some 190 ∧ outcome=.push 190 (.stay 189)) ∨
 (dir=.east ∧ source=some 216 ∧ outcome=.push 216 (.stay 217))

theorem FirstCut.head_cases {dirs final pushes moves outcomes}
    (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes) :
    HeadCases cut.direction cut.actor.pushSource cut.headOutcome := by
  obtain ⟨source,_,metadata,paid⟩ := cut.headPaid
  have holesInside := cut.before.logged.trace.holes_sublist.subset
  rcases paid with ⟨rfl,directionEq⟩ | ⟨rfl,directionEq⟩ | ⟨rfl,directionEq⟩ | ⟨rfl,dirs⟩ | ⟨rfl,dirs⟩ | ⟨rfl,directionEq⟩
  · have target : pushTargets soko1_1.board 137 cut.direction=[136] := by rw [directionEq]; decide +kernel
    have head := ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
    exact Or.inl ⟨directionEq,metadata,head⟩
  · have target : pushTargets soko1_1.board 139 cut.direction=[140] := by rw [directionEq]; decide +kernel
    have head := ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
    exact Or.inr (Or.inl ⟨directionEq,metadata,head⟩)
  · have target : pushTargets soko1_1.board 191 cut.direction=[192] := by rw [directionEq]; decide +kernel
    have head := ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
    exact Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩))
  · rcases dirs with directionEq|directionEq
    · have target : pushTargets soko1_1.board 138 cut.direction=[139] := by rw [directionEq]; decide +kernel
      have head := ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩)))
    · have target : pushTargets soko1_1.board 138 cut.direction=[137] := by rw [directionEq]; decide +kernel
      have head := ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩))))
  · rcases dirs with directionEq|directionEq
    · have target : pushTargets soko1_1.board 190 cut.direction=[191] := by rw [directionEq]; decide +kernel
      have head := ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩)))))
    · have target : pushTargets soko1_1.board 190 cut.direction=[189] := by rw [directionEq]; decide +kernel
      have head := ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨directionEq,metadata,head⟩))))))
  · have target : pushTargets soko1_1.board 216 cut.direction=[217] := by rw [directionEq]; decide +kernel
    have head := ordinary_effect cut.headChecked cut.headEffect metadata target (by decide +kernel) holesInside
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨directionEq,metadata,head⟩)))))))
#print axioms FirstCut.head_cases
end Owner1007.UpperHeadCases11
