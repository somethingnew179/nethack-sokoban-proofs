import Owner1007.Q190Upper11
import Owner1007.Budget32711
namespace Owner1007.Q190Upper11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem upper_eight {state final : State} {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤8)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)≤4)
 (zero137 : ownPushes [137] before=0) (zero139 : ownPushes [139] before=0)
 (prefixFour : 4≤energy soko1_1.initial state UpperBudget11.U6 before)
 (i : Fin 3) (selected : locks i⊆endGroup UpperBudget11.U6 before) (hero : state.player∈region i) :
 8≤energy soko1_1.initial final UpperBudget11.U6 (before++outcomes) := by
 have actual:=(NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace).1
 have beforeFacts:=first.end_subset (by decide) UpperBudget11.U6 (by decide) (by decide)
 have inside:=List.Subset.trans selected beforeFacts.2
 have allGone:=Budget32711.upper_gone (first.append logged) completed upperCap
 rw [endGroup_append] at allGone
 have mono:=logged.end_mono actual (locks i) (endGroup UpperBudget11.U6 before) (unique i) inside selected
 have smallGone : endGroup (locks i) outcomes=[]:=by
  rw [allGone] at mono
  exact List.eq_nil_iff_forall_not_mem.mpr (by intro c h;simpa using mono h)
 have future:=future_four first logged completed upperCap restCap zero137 zero139
  (locks i) (unique i) inside i (List.Perm.refl _) hero smallGone
 have nested:=energy_subset first.trace logged (locks i) (endGroup UpperBudget11.U6 before)
  (unique i) beforeFacts.1 selected beforeFacts.2
  (by have len:=endGroup_length_le UpperBudget11.U6 before;have six : UpperBudget11.U6.length=6:=rfl;rw [six] at len;omega)
 have split:=energy_append soko1_1.initial state final UpperBudget11.U6 before outcomes
 omega
#print axioms upper_eight
end Owner1007.Q190Upper11
