import Owner1007.PairResetFuture11
import Owner1007.UpperBudget11
import Owner1007.LoggedAppend11
import Owner1007.HeroEnergySubset11
import NetHack.Sokoban.Reduction
namespace Owner1007.ForwardResetEight11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem upper_eight {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .east=some t) (effect : Matches state t (.push 190 (.stay 191)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (same : (endGroup TightSplit11.A before).Perm [139,190])
 (prefixTwo : 2≤energy soko1_1.initial state TightSplit11.A before)
 (otherTwo : 2≤energy soko1_1.initial final [188] (before++.push 190 (.stay 191)::after)) :
 8≤energy soko1_1.initial final UpperBudget11.U6 (before++.push 190 (.stay 191)::after) := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have selected := first.end_subset (by decide) TightSplit11.A (by decide) (by decide)
 have sourceEq : t.pushSource=some 190 := by rw [effect.2]
 have owner : 190∈endGroup TightSplit11.A before := same.mem_iff.mpr (by decide)
 have row := PairStrict11.exit_row scalar rfl valid head effect selected.1 selected.2
  ⟨190,owner,sourceEq,by simp [PairActor11.Exit]⟩
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup TightSplit11.A before) (.push 190 (.stay 191))+
  value t.state (update (endGroup TightSplit11.A before) (.push 190 (.stay 191)))-value state (endGroup TightSplit11.A before) at row
 have nextSame : (update (endGroup TightSplit11.A before) (.push 190 (.stay 191))).Perm [139,191] :=
  (update_perm same _).trans (by decide +kernel)
 have actual := step_boulders_nodup _ _ _ _ valid.1 head
 have nextInside := GhostSubset.update_subset _ _ _ effect _ selected.1 selected.2
 have pairInside : [139,191]⊆t.state.boulders := fun c member=>nextInside (nextSame.mem_iff.mpr member)
 have afterReached := first.trace.append (Trace.cons head (Trace.nil t.state))
 have hero : t.state.player∈([138,190] : List Cell) := by rw [effect.2];change (190:Cell)∈[138,190];decide
 obtain ⟨phase,atIndex⟩:=valid.2
 have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
 have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
   (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq];exact atIndex
 have activeBefore : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16 :=
  HazardPhaseCountedCorrection.active_of_step _ _ within _ _ head
 have holesSame : t.state.holes=state.holes := by rw [effect.2]
 have active : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes t.state<16 := by
  simpa only [HazardPhaseCountedCorrection.phaseOf,holesSame] using activeBefore
 have future := PairResetFuture11.future_two afterReached last completed active hero pairInside
 have equal := energy_perm nextSame t.state final after
 have tailTwo : 2≤energy t.state final (update (endGroup TightSplit11.A before) (.push 190 (.stay 191))) after := by
  change energy t.state final (update (endGroup TightSplit11.A before) (.push 190 (.stay 191))) after=
   energy t.state final [139,191] after at equal
  omega
 have split := energy_append soko1_1.initial state final TightSplit11.A before (.push 190 (.stay 191)::after)
 have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight state t.state final
  (endGroup TightSplit11.A before) (.push 190 (.stay 191)) after
 change energy state final (endGroup TightSplit11.A before) (.push 190 (.stay 191)::after)=
  charge NetHack.Soko11Hero315.holeWeight (endGroup TightSplit11.A before) (.push 190 (.stay 191))+
  value t.state (update (endGroup TightSplit11.A before) (.push 190 (.stay 191)))-value state (endGroup TightSplit11.A before)+
  energy t.state final (update (endGroup TightSplit11.A before) (.push 190 (.stay 191))) after at one
 have pairSix : 6≤energy soko1_1.initial final TightSplit11.A (before++.push 190 (.stay 191)::after) := by omega
 let headLogged : Logged soko1_1.board state [.east] t.state t.pushCost 1 [.push 190 (.stay 191)] := .cons head effect (.nil _)
 let full := (first.append headLogged).append last
 have partition := energy_split full TightSplit11.A [188] (by decide) (by decide)
 have bound := energy_subset (Trace.nil soko1_1.initial) full (TightSplit11.A++[188]) UpperBudget11.U6
  (by decide) (by decide) (by decide) (by decide) (by decide)
 change energy soko1_1.initial final (TightSplit11.A++[188]) ((before++[.push 190 (.stay 191)])++after)=
   energy soko1_1.initial final TightSplit11.A ((before++[.push 190 (.stay 191)])++after)+
   energy soko1_1.initial final [188] ((before++[.push 190 (.stay 191)])++after) at partition
 simp only [List.append_assoc,List.singleton_append] at partition bound
 omega
#print axioms upper_eight
end Owner1007.ForwardResetEight11
