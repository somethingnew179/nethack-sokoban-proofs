import Owner1007.FirstAboveMate11
import Owner1007.BeforeAboveOther11
import Owner1007.AboveOtherZero11
import Owner1007.ModeC264Mass11
import Owner1007.Gate265FirstBelow11
namespace Owner1007.ModeCFirstBelow11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.ModeC264Mass11 (Other)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_above {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : pushes≤327) (left : energy soko1_1.initial final TightSplit11.B outcomes≤4)
 (rest : energy soko1_1.initial final UpperBudget11.Rest outcomes≤2)
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes)
 (above : boundary.actor.pushSource=some 239 ∧boundary.direction=.south) : False := by
 have price := FirstAboveMate11.marker264_two logged completed (by omega) rest boundary above
 have other := (ModeC264Mass11.other_zero logged rest price).1
 have stationary := ModeC264Mass11.stationary321 logged completed cheap left rest price
 have initial := BeforeAboveOther11.initial logged completed other stationary boundary above
 have target : pushTargets soko1_1.board 239 boundary.direction=[265] := by rw [above.2];decide +kernel
 have headEq := UpperHeadCases11.ordinary_effect boundary.headChecked boundary.headEffect above.1 target
   (by decide +kernel) boundary.before.logged.trace.holes_sublist.subset
 have effect : Matches boundary.middle boundary.actor (.push 239 (.stay 265)) := by simpa only [headEq] using boundary.headEffect
 let one : Logged soko1_1.board boundary.middle [boundary.direction] boundary.actor.state boundary.actor.pushCost 1 [boundary.headOutcome] :=
   .cons boundary.headChecked boundary.headEffect (.nil _)
 let first := boundary.before.logged.append one
 let effects := boundary.beforeOutcomes++[boundary.headOutcome]
 have tagG : endGroup BeforeAboveOther11.G effects=BeforeAboveOther11.G := by
  rw [endGroup_append,initial]
  change update BeforeAboveOther11.G boundary.headOutcome=BeforeAboveOther11.G
  rw [headEq]
  decide
 have included := end_subset_selected first (by decide) BeforeAboveOther11.G Other
   (by decide) (by decide) (by decide) (by decide)
 have owns : AboveOther11.G⊆endGroup Other effects := by
  intro c h
  exact included (by rw [tagG];exact h)
 have eqEffects : effects++boundary.afterOutcomes=outcomes := by
  simpa only [effects,List.append_assoc,List.singleton_append] using boundary.outcomesEq.symm
 have zero : energy soko1_1.initial final Other (effects++boundary.afterOutcomes)=0 := by rw [eqEffects];exact other
 have hero : boundary.actor.state.player=239 := by rw [effect.2]
 have front : 265∈boundary.actor.state.boulders := by rw [effect.2];simp
 exact AboveOtherZero11.impossible first boundary.after completed zero owns front hero

theorem below {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cheap : pushes≤327) (left : energy soko1_1.initial final TightSplit11.B outcomes≤4)
 (rest : energy soko1_1.initial final UpperBudget11.Rest outcomes≤2)
 (boundary : FirstCut Gate265Transport11.paid soko1_1.initial soko1_1.initial.boulders dirs final pushes moves outcomes) :
 ∃source,source∈endGroup UpperBudget11.Rest boundary.beforeOutcomes ∧
  boundary.actor.pushSource=some source ∧
  ((source=264∧boundary.direction=.east)∨(source=266∧boundary.direction=.west)∨(source=291∧boundary.direction=.north)) := by
 obtain ⟨source,owner,metadata,pays⟩ := boundary.headPaid
 rcases pays with ⟨rfl,south⟩|⟨rfl,east⟩|⟨rfl,west⟩|⟨rfl,north⟩
 ·exact False.elim (not_above logged completed cheap left rest boundary ⟨metadata,south⟩)
 ·exact ⟨264,Gate265FirstBelow11.lower_owner boundary 264 (by decide) owner,metadata,Or.inl ⟨rfl,east⟩⟩
 ·exact ⟨266,Gate265FirstBelow11.lower_owner boundary 266 (by decide) owner,metadata,Or.inr (Or.inl ⟨rfl,west⟩)⟩
 ·exact ⟨291,Gate265FirstBelow11.lower_owner boundary 291 (by decide) owner,metadata,Or.inr (Or.inr ⟨rfl,north⟩)⟩
#print axioms not_above
#print axioms below
end Owner1007.ModeCFirstBelow11
