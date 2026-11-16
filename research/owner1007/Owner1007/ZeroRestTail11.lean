import Owner1007.HeroEnergySubset11
import Owner1007.HeroEnergyTrace11
import Owner1007.UpperBudget11
namespace Owner1007.ZeroRestTail11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem subset_zero {beforeDirs state beforePushes beforeMoves before afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state afterDirs final afterPushes afterMoves after)
 (zero : energy soko1_1.initial final UpperBudget11.Rest (before++after)=0)
 (group : List Cell) (groupUnique : group.Nodup) (subset : group⊆endGroup UpperBudget11.Rest before) :
 energy state final group after=0 := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant first.trace
 have selected := first.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 have restBound := endGroup_length_le UpperBudget11.Rest before
 have restSize : (endGroup UpperBudget11.Rest before).length≤18 := by
   change (endGroup UpperBudget11.Rest before).length≤10 at restBound
   omega
 have inside := List.Subset.trans subset selected.2
 have groupBound := List.Nodup.length_le_of_subset groupUnique subset
 have groupSize : group.length≤18 := Nat.le_trans groupBound restSize
 have prefixNN := energy_nonnegative first UpperBudget11.Rest (by decide) (by decide)
 have split := energy_append soko1_1.initial state final UpperBudget11.Rest before after
 have compare := energy_subset first.trace last group (endGroup UpperBudget11.Rest before)
   groupUnique selected.1 subset selected.2 restSize
 have nn := HeroLedger.Logged.energy_nonnegative last (groupCertificate 18) valid group groupUnique inside groupSize
 change 0≤energy state final group after at nn
 omega
theorem active_after_stay {prior state priorPushes priorMoves dir t source landing}
 (reached : Trace soko1_1.board soko1_1.initial prior state priorPushes priorMoves)
 (head : step soko1_1.board state dir=some t)
 (effect : Matches state t (.push source (.stay landing))) :
 HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes t.state<16 := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 obtain ⟨phase,atIndex⟩ := valid.2
 have phaseEq := HazardPhaseCountedCorrection.at_phase NetHack.SokobanLinearPhases.Map11.certificate phase state atIndex
 have within : HazardPhases.At NetHack.SokobanLinearPhases.Map11.certificate
     (HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state) state := by rw [←phaseEq];exact atIndex
 have beforeActive : HazardPhaseCountedCorrection.phaseOf soko1_1.initial.holes state<16 :=
   HazardPhaseCountedCorrection.active_of_step _ _ within _ _ head
 have holesSame : t.state.holes=state.holes := by rw [effect.2]
 simpa only [HazardPhaseCountedCorrection.phaseOf,holesSame] using beforeActive
#print axioms subset_zero
#print axioms active_after_stay
end Owner1007.ZeroRestTail11