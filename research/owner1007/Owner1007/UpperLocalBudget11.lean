import Owner1007.UpperLocalCuts11
import Owner1007.CutEnergy11
import Owner1007.HeroEndSubset11
namespace Owner1007.UpperLocalBudget11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11

def next {state small dirs final pushes moves outcomes}
 (cut : FirstCut UpperZero11.paid state small dirs final pushes moves outcomes) (big : List Cell) :=
 update (endGroup big cut.beforeOutcomes) cut.headOutcome

theorem next_facts {state small dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut UpperZero11.paid state small dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (big : List Cell) (unique : big.Nodup) (inside : big⊆state.boulders) (bounded : big.length≤18) :
 (next cut big).Nodup ∧ next cut big⊆cut.actor.state.boulders ∧ (next cut big).length≤18 := by
 have actual := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached).1
 have before := cut.before.logged.end_subset actual big unique inside
 have current := (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant (reached.append cut.before.logged.trace)).1
 have afterActual := step_boulders_nodup _ _ _ _ current cut.headChecked
 have unq := GhostSubset.update_unique _ _ _ cut.headEffect afterActual _ before.1 before.2
 have sub := GhostSubset.update_subset _ _ _ cut.headEffect _ before.1 before.2
 have lenBefore := endGroup_length_le big cut.beforeOutcomes
 have lenAfter := update_length (endGroup big cut.beforeOutcomes) cut.headOutcome
 exact ⟨unq,sub,by change (update (endGroup big cut.beforeOutcomes) cut.headOutcome).length≤18; omega⟩
#print axioms next_facts

theorem two_tail_le {state small dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut UpperZero11.paid state small dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (smallUnique : small.Nodup) (big : List Cell) (unique : big.Nodup)
 (inside : big⊆state.boulders) (bounded : big.length≤18) (included : small⊆big) :
 2+energy cut.actor.state final (next cut big) cut.afterOutcomes≤energy state final big outcomes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have before := cut.before.logged.end_subset valid.1 big unique inside
 have current := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant (reached.append cut.before.logged.trace)
 have subset := end_subset_selected cut.before.logged valid.1 small big smallUnique unique included inside
 obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
 have row := CutStrict11.exit_row scalar rfl current cut.headChecked cut.headEffect before.1 before.2
   ⟨source,subset owner,metadata,CutEnergy11.upper_paid source cut.direction pays⟩
 change 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup big cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (next cut big)-value cut.middle (endGroup big cut.beforeOutcomes) at row
 have nn := HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 18) valid big unique inside bounded
 change 0≤energy state cut.middle big cut.beforeOutcomes at nn
 have split := energy_append state cut.middle final big cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
   (endGroup big cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup big cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
   charge NetHack.Soko11Hero315.holeWeight (endGroup big cut.beforeOutcomes) cut.headOutcome+
   value cut.actor.state (next cut big)-value cut.middle (endGroup big cut.beforeOutcomes)+
   energy cut.actor.state final (next cut big) cut.afterOutcomes at one
 have same := congrArg (energy state final big) cut.outcomesEq
 omega
#print axioms two_tail_le
end Owner1007.UpperLocalBudget11
