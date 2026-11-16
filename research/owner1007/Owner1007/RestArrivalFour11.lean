import Owner1007.RestArrivalTwo11
import Owner1007.TightSurvivors11
namespace Owner1007.RestArrivalFour11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.RestArrivalTwo11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem singleton_exit {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (cell : Cell) (_initial : cell∈soko1_1.initial.boulders) (colored : cell∈carrier)
 (gone : endGroup [cell] outcomes=[]) :
 Nonempty (FirstCut paid soko1_1.initial [cell] dirs final pushes moves outcomes) := by
 rcases first_cut_or_quiet (paid:=paid) logged [cell] with found|quiet
 ·exact found
 ·have noholes : ∀c∈carrier,c∉soko1_1.initial.holes := by decide +kernel
  have moved := TransportQuiet11.Quiet.transport quiet carrier closed (by simpa using colored) true
    (by intro _ c h;exact noholes c h) (by simp)
  have retained := moved.2 rfl
  rw [gone] at retained
  contradiction

theorem side_two {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (cell : Cell) (inRest : cell∈UpperBudget11.Rest) (colored : cell∈carrier)
 (gone : endGroup [cell] outcomes=[])
 (noNorth : PaidCount11.count FirstRest18711.paid UpperBudget11.Rest dirs outcomes=0) :
 2≤energy soko1_1.initial final [cell] outcomes := by
 have initial : cell∈soko1_1.initial.boulders := (show UpperBudget11.Rest⊆soko1_1.initial.boulders from by decide) inRest
 obtain ⟨cut⟩ := singleton_exit logged cell initial colored gone
 obtain ⟨source,owner,metadata,same,shape⟩ := cut.headPaid
 subst source
 have inclusion := end_subset_selected cut.before.logged (by decide) [cell] UpperBudget11.Rest
   (by simp) (by decide) (by simpa using inRest) (by decide)
 have restOwner : 213∈endGroup UpperBudget11.Rest cut.beforeOutcomes := inclusion owner
 rcases shape with north|east|west
 ·have pays : OwnedCorral11.PaidStep FirstRest18711.paid
      (endGroup UpperBudget11.Rest cut.beforeOutcomes) cut.direction cut.actor :=
    ⟨213,restOwner,metadata,⟨rfl,north⟩⟩
  have positive := PaidCount11.event_le (paid:=FirstRest18711.paid)
    (lastDirs:=cut.afterDirs) (last:=cut.afterOutcomes)
    cut.before.logged cut.headEffect UpperBudget11.Rest pays
  rw [←cut.dirsEq,←cut.outcomesEq,noNorth] at positive
  omega
 ·have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
  have selected := cut.before.logged.end_subset (by decide) [cell] (by simp) (by simpa using initial)
  have pays : UpperLocalPrice11.paid 213 cut.direction := by rw [east];decide
  have row := UpperLocalPrice11.exit_row valid selected.1 selected.2
    cut.headChecked cut.headEffect ⟨213,owner,metadata,pays⟩
  have gap := logged_event_gap_le cut.before.logged cut.headChecked cut.headEffect cut.after
    [cell] (by simp) (by simpa using initial)
  rw [←cut.outcomesEq] at gap
  exact Int.le_trans row gap
 ·have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
  have selected := cut.before.logged.end_subset (by decide) [cell] (by simp) (by simpa using initial)
  have pays : UpperLocalPrice11.paid 213 cut.direction := by rw [west];decide
  have row := UpperLocalPrice11.exit_row valid selected.1 selected.2
    cut.headChecked cut.headEffect ⟨213,owner,metadata,pays⟩
  have gap := logged_event_gap_le cut.before.logged cut.headChecked cut.headEffect cut.after
    [cell] (by simp) (by simpa using initial)
  rw [←cut.outcomesEq] at gap
  exact Int.le_trans row gap

theorem first_cut {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (restCheap : energy soko1_1.initial final UpperBudget11.Rest outcomes<4) :
 Nonempty (FirstCut FirstRest18711.paid soko1_1.initial UpperBudget11.Rest dirs final pushes moves outcomes) := by
 rcases first_cut_or_quiet (paid:=FirstRest18711.paid) logged UpperBudget11.Rest with found|quiet
 ·exact found
 ·have noNorth := FirstRest18711.quiet_count_zero quiet
  have consume (cell : Cell) (member : cell∈([264,266] : List Cell)) : endGroup [cell] outcomes=[] := by
   apply TightSurvivors11.singleton_nil logged completed UpperBudget11.Rest (by decide) (by decide) (by decide) 3 (by omega)
     cell ((show ([264,266] : List Cell)⊆UpperBudget11.Rest from by decide) member)
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl <;> decide +kernel
  have two264 := side_two logged 264 (by decide) (by decide) (consume 264 (by decide)) noNorth
  have two266 := side_two logged 266 (by decide) (by decide) (consume 266 (by decide)) noNorth
  have split := HeroLedger.Logged.energy_split logged (by decide) weightAt NetHack.Soko11Hero315.holeWeight
    [264] [266] (by decide) (by decide)
  change energy soko1_1.initial final [264,266] outcomes=
    energy soko1_1.initial final [264] outcomes+energy soko1_1.initial final [266] outcomes at split
  have compare := energy_subset (Trace.nil soko1_1.initial) logged [264,266] UpperBudget11.Rest
    (by decide) (by decide) (by decide) (by decide) (by decide)
  omega
#print axioms singleton_exit
#print axioms side_two
#print axioms first_cut
end Owner1007.RestArrivalFour11
