import Owner1007.CanonicalArrival18711
import Owner1007.PaidCount11
namespace Owner1007.FirstRest18711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
def paid (source : Cell) (dir : Dir) : Prop := source=213∧dir=.north
instance (source : Cell) (dir : Dir) : Decidable (paid source dir) := by unfold paid;infer_instance

theorem quiet_count_zero {paid state group dirs final pushes moves outcomes}
 [∀c d,Decidable (paid c d)]
 (quiet : UpperQuiet11.Quiet paid state group dirs final pushes moves outcomes) :
 PaidCount11.count paid group dirs outcomes=0 := by
 induction quiet with
 |nil=>rfl
 |@cons state group dir t rest final pushes moves outcome outcomes head effect avoid tail ih=>
   have noOwn : ¬PaidCount11.owned paid group dir outcome := fun own=>avoid ((PaidCount11.owned_iff effect).mp own)
   simpa only [PaidCount11.count,if_neg noOwn,Nat.zero_add] using ih

theorem first_cut {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325) :
 Nonempty (FirstCut paid soko1_1.initial UpperBudget11.Rest dirs final pushes moves outcomes) := by
 obtain ⟨arrival⟩ := CanonicalArrival18711.canonical logged completed cheap
 rcases first_cut_or_quiet (paid:=paid) logged UpperBudget11.Rest with found|quiet
 · exact found
 · have countZero := quiet_count_zero quiet
   have metadata : arrival.actor.pushSource=some 213 := by rw [arrival.effect.2]
   have pays : OwnedCorral11.PaidStep paid (endGroup UpperBudget11.Rest arrival.beforeOutcomes) .north arrival.actor :=
     ⟨213,arrival.owner,metadata,⟨rfl,rfl⟩⟩
   have countPos := PaidCount11.event_le (paid:=paid) (lastDirs:=arrival.afterDirs) (last:=arrival.afterOutcomes)
     arrival.first arrival.effect UpperBudget11.Rest pays
   rw [←arrival.dirsEq,←arrival.outcomesEq] at countPos
   omega
theorem head_shape {dirs final pushes moves outcomes}
 (cut : FirstCut paid soko1_1.initial UpperBudget11.Rest dirs final pushes moves outcomes) :
 cut.actor.pushSource=some 213 ∧cut.direction=.north ∧cut.headOutcome=.push 213 (.stay 187) := by
 obtain ⟨source,owner,metadata,same,north⟩ := cut.headPaid
 subst source
 have target : pushTargets soko1_1.board 213 cut.direction=[187] := by rw [north];decide +kernel
 have headEq := UpperHeadCases11.ordinary_effect cut.headChecked cut.headEffect metadata target
   (by decide +kernel) cut.before.logged.trace.holes_sublist.subset
 exact ⟨metadata,north,headEq⟩
#print axioms first_cut
#print axioms head_shape
end Owner1007.FirstRest18711
