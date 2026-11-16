import Owner1007.CutEnergy11
import Owner1007.UpperBudget11
import Owner1007.HeroEndSubset11
import Owner1007.UpperLocalPrice11
import Owner1007.LoggedAppend11
namespace Owner1007.UpperExtraWestEight11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem upper_eight {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 188 (.stay 187)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (same : (endGroup [137,139,191] before).Perm [137,139,190])
 (tag188 : endGroup [188] before=[188])
 (prefixFour : 4≤energy soko1_1.initial state UpperBudget11.U6 before) :
 8≤energy soko1_1.initial final UpperBudget11.U6 (before++.push 188 (.stay 187)::after) := by
 have valid:=NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have selected:=first.end_subset (by decide) UpperBudget11.U6 (by decide) (by decide)
 have small:=first.end_subset (by decide) [137,139,191] (by decide) (by decide)
 have nested:=end_subset_selected first (by decide) [137,139,191] UpperBudget11.U6 (by decide) (by decide) (by decide) (by decide)
 have own188:=end_subset_selected first (by decide) [188] UpperBudget11.U6 (by decide) (by decide) (by decide) (by decide)
 have owner : 188∈endGroup UpperBudget11.U6 before := own188 (by rw [tag188];simp)
 have sourceEq : t.pushSource=some 188 := by rw [effect.2]
 have row:=UpperLocalPrice11.exit_row valid selected.1 selected.2 head effect
  ⟨188,owner,sourceEq,by simp [UpperLocalPrice11.paid,UpperLocalPrice11.westSources]⟩
 have nextSame : (update (endGroup [137,139,191] before) (.push 188 (.stay 187))).Perm [137,139,190] :=
  (update_perm same _).trans (by decide +kernel)
 have lifted:=update_mono (endGroup [137,139,191] before) (endGroup UpperBudget11.U6 before) small.1 nested (.push 188 (.stay 187))
 have subset : [137,139,190]⊆update (endGroup UpperBudget11.U6 before) (.push 188 (.stay 187)) :=
  fun c member=>lifted (nextSame.mem_iff.mpr member)
 have actual:=step_boulders_nodup _ _ _ _ valid.1 head
 have nextUnique:=GhostSubset.update_unique _ _ _ effect actual _ selected.1 selected.2
 have nextInside:=GhostSubset.update_subset _ _ _ effect _ selected.1 selected.2
 have groupInside : [137,139,190]⊆t.state.boulders := List.Subset.trans subset nextInside
 have afterReached:=first.trace.append (Trace.cons head (Trace.nil t.state))
 have nextHero : t.state.player∈UpperZero11.region 12 := by
  rw [effect.2]
  change 188∈UpperZero11.region 12
  decide +kernel
 have good : OwnedCorral11.Good UpperZero11.locks UpperZero11.region t.state [137,139,190] := ⟨12,nextHero,by intro c h;exact h⟩
 have future:=CutEnergy11.future_energy UpperZero11.closed UpperZero11.unique UpperZero11.size (by decide) CutEnergy11.upper_paid
  afterReached last completed [137,139,190] (by decide) groupInside (by decide) good
 have lengthBefore:=endGroup_length_le UpperBudget11.U6 before
 have lengthAfter:=update_length (endGroup UpperBudget11.U6 before) (.push 188 (.stay 187))
 have bound:=energy_subset afterReached last [137,139,190] (update (endGroup UpperBudget11.U6 before) (.push 188 (.stay 187)))
  (by decide) nextUnique subset nextInside (by have six : UpperBudget11.U6.length=6:=rfl;rw [six] at lengthBefore;omega)
 have tailTwo : 2≤energy t.state final (update (endGroup UpperBudget11.U6 before) (.push 188 (.stay 187))) after := by omega
 have split:=energy_append soko1_1.initial state final UpperBudget11.U6 before (.push 188 (.stay 187)::after)
 have one:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final
  (endGroup UpperBudget11.U6 before) (.push 188 (.stay 187)) after
 change energy state final (endGroup UpperBudget11.U6 before) (.push 188 (.stay 187)::after)=
  charge NetHack.Soko11Hero315.holeWeight (endGroup UpperBudget11.U6 before) (.push 188 (.stay 187))+
  value t.state (update (endGroup UpperBudget11.U6 before) (.push 188 (.stay 187)))-value state (endGroup UpperBudget11.U6 before)+
  energy t.state final (update (endGroup UpperBudget11.U6 before) (.push 188 (.stay 187))) after at one
 omega
#print axioms upper_eight
end Owner1007.UpperExtraWestEight11
