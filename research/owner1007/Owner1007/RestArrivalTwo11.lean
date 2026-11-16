import Owner1007.Gate265Transport11
import Owner1007.UpperLocalPrice11
namespace Owner1007.RestArrivalTwo11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11

/- A holes-free transport carrier, not a boulder-configuration table. -/
def carrier : List Cell := [213,239,265]++Gate265Transport11.lower
def paid (source : Cell) (dir : Dir) : Prop :=
 source=213 ∧ (dir=.north ∨ dir=.east ∨ dir=.west)
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance
def check (dir : Dir) : Bool := carrier.all fun source=>if paid source dir then true else
 (pushTargets soko1_1.board source dir).all (fun dest=>decide (dest∈carrier))
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem checks : allDirs.all check=true := by decide +kernel
theorem closed : ∀source dir dest,source∈carrier→¬paid source dir→
 dest∈pushTargets soko1_1.board source dir→dest∈carrier := by
 intro source dir dest member unpaid target
 have row := List.all_eq_true.mp (List.all_eq_true.mp checks dir (Geometry.all_directions dir)) source member
 simp only [if_neg unpaid] at row
 exact of_decide_eq_true (List.all_eq_true.mp row dest target)

theorem exit_exists {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) :
 Nonempty (FirstCut paid soko1_1.initial Gate265Transport11.lowerOrigins dirs final pushes moves outcomes) := by
 rcases first_cut_or_quiet (paid:=paid) logged Gate265Transport11.lowerOrigins with found|quiet
 · exact found
 · have noholes : ∀c∈carrier,c∉soko1_1.initial.holes := by decide +kernel
   have moved := TransportQuiet11.Quiet.transport quiet carrier closed (by decide +kernel) true
     (by intro _ c member;exact noholes c member) (by simp)
   have selected := logged.end_subset (by decide) Gate265Transport11.lowerOrigins (by decide) (by decide)
   have card := List.Nodup.length_le_of_subset selected.1 selected.2
   have conservation := logged.trace.conservation
   have empty : final.holes=[] := completed
   rw [empty] at conservation
   change 18+0=final.boulders.length+16 at conservation
   have retained := moved.2 rfl
   change (endGroup Gate265Transport11.lowerOrigins outcomes).length=8 at retained
   omega

/- Any completion with Rest energy below two already has a Rest-owned 213N187.
   No stationary spare, lower-corridor schedule, or push-count cap is assumed. -/
theorem first_cut {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final)
 (restCheap : energy soko1_1.initial final UpperBudget11.Rest outcomes<2) :
 Nonempty (FirstCut FirstRest18711.paid soko1_1.initial UpperBudget11.Rest dirs final pushes moves outcomes) := by
 obtain ⟨cut⟩ := exit_exists logged completed
 obtain ⟨source,owner,metadata,same,shape⟩ := cut.headPaid
 subst source
 have inclusion := end_subset_selected cut.before.logged (by decide)
   Gate265Transport11.lowerOrigins UpperBudget11.Rest
   (by decide) (by decide) (by decide) (by decide)
 have restOwner : 213∈endGroup UpperBudget11.Rest cut.beforeOutcomes := inclusion owner
 rcases shape with north|east|west
 · rcases first_cut_or_quiet (paid:=FirstRest18711.paid) logged UpperBudget11.Rest with found|quiet
   · exact found
   · have zero := FirstRest18711.quiet_count_zero quiet
     have pays : OwnedCorral11.PaidStep FirstRest18711.paid
         (endGroup UpperBudget11.Rest cut.beforeOutcomes) cut.direction cut.actor :=
       ⟨213,restOwner,metadata,⟨rfl,north⟩⟩
     have positive := PaidCount11.event_le (paid:=FirstRest18711.paid)
       (lastDirs:=cut.afterDirs) (last:=cut.afterOutcomes)
       cut.before.logged cut.headEffect UpperBudget11.Rest pays
     rw [←cut.dirsEq,←cut.outcomesEq] at positive
     omega
 · have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
   have selected := cut.before.logged.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
   have pays : UpperLocalPrice11.paid 213 cut.direction := by rw [east];decide
   have row := UpperLocalPrice11.exit_row valid selected.1 selected.2
     cut.headChecked cut.headEffect ⟨213,restOwner,metadata,pays⟩
   have bound := logged_event_gap_le cut.before.logged cut.headChecked cut.headEffect cut.after
     UpperBudget11.Rest (by decide) (by decide)
   rw [←cut.outcomesEq] at bound
   omega
 · have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant cut.before.logged.trace
   have selected := cut.before.logged.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
   have pays : UpperLocalPrice11.paid 213 cut.direction := by rw [west];decide
   have row := UpperLocalPrice11.exit_row valid selected.1 selected.2
     cut.headChecked cut.headEffect ⟨213,restOwner,metadata,pays⟩
   have bound := logged_event_gap_le cut.before.logged cut.headChecked cut.headEffect cut.after
     UpperBudget11.Rest (by decide) (by decide)
   rw [←cut.outcomesEq] at bound
   omega

#print axioms checks
#print axioms exit_exists
#print axioms first_cut
end Owner1007.RestArrivalTwo11
