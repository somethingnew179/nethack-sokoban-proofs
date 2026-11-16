import Owner1007.UpperFirstCut11
import Owner1007.ActorPrices11
namespace Owner1007.Upper190History11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.UpperQuiet11 Owner1007.UpperFirstCut11

theorem phase190_checked :
    (List.finRange 19).all (fun i => decide
      (190 ∉ UpperZero11.locks i ∨ 191 ∉ UpperZero11.region i ∨ i.val=12)) = true := by decide +kernel

theorem push_adjacent {state : State} {dir : Dir} {t : Transition} {source : Cell}
    (checked : step soko1_1.board state dir = some t) (sourceEq : t.pushSource=some source) :
    advance soko1_1.board state.player dir=some source := by
  rcases step_cases_full _ _ _ _ checked with walked | pushed
  · obtain ⟨target,_,_,_,_,shape⟩ := walked
    simp only [shape] at sourceEq
    contradiction
  · obtain ⟨other,result,adjacent,_,_,_,shape⟩ := pushed
    have same : other=source := by simpa only [shape,Option.some.injEq] using sourceEq
    simpa only [same] using adjacent

theorem FirstCut.stationary_before_190west {dirs final pushes moves outcomes}
    (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
    (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.west) :
    ownPushes [137] cut.beforeOutcomes=0 ∧ ownPushes [139] cut.beforeOutcomes=0 := by
  have good := quiet_good UpperZero11.closed cut.before (by decide) (by decide) (by decide) (by decide)
    original_good (by simp)
  obtain ⟨i,heroInside,inside⟩ := good
  have bounded := endGroup_length_le originalGroup cut.beforeOutcomes
  change (endGroup originalGroup cut.beforeOutcomes).length ≤ 3 at bounded
  obtain ⟨source,owner,metadata,_⟩ := cut.headPaid
  have same : source=190 := Option.some.inj (metadata.symm.trans sourceEq)
  have present : 190 ∈ endGroup originalGroup cut.beforeOutcomes := same ▸ owner
  have locked := lock_complete i (endGroup originalGroup cut.beforeOutcomes) bounded inside 190 present
  have adjacent := push_adjacent cut.headChecked sourceEq
  rw [directionEq] at adjacent
  have hero := ActorPrices11.support_of_check 190 cut.middle.player .west 191
    (by decide +kernel) (step_player_clear _ _ _ _ cut.headChecked).1 adjacent
  have hero191 : 191 ∈ UpperZero11.region i := by simpa only [hero] using heroInside
  have row := of_decide_eq_true (List.all_eq_true.mp phase190_checked i (by simp))
  have phase : i.val=12 := by
    rcases row with outside | outside | phase
    · exact False.elim (outside locked)
    · exact False.elim (outside hero191)
    · exact phase
  have index : i=⟨12,by decide⟩ := Fin.ext phase
  have seen137 : 137 ∈ endGroup originalGroup cut.beforeOutcomes := inside (by rw [index]; decide +kernel)
  have seen139 : 139 ∈ endGroup originalGroup cut.beforeOutcomes := inside (by rw [index]; decide +kernel)
  exact ⟨cut.before.stationary UpperZero11.closed (by decide) (by decide) (by decide) (by decide)
      original_good (by simp) 137 (by simp) seen137,
    cut.before.stationary UpperZero11.closed (by decide) (by decide) (by decide) (by decide)
      original_good (by simp) 139 (by simp) seen139⟩

#print axioms FirstCut.stationary_before_190west
end Owner1007.Upper190History11
