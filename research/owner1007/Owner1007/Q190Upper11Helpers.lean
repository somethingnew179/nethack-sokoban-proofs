import Owner1007.Q190Upper11Data
import Owner1007.CutEnergy11
import Owner1007.StrongShaftGate11
import Owner1007.HeroEnergySubset11
namespace Owner1007.Q190Upper11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
theorem cut_four {predicate state group dirs final pushes moves outcomes history past pastMoves}
 (cut : FirstCut predicate state group dirs final pushes moves outcomes)
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (uniqueGroup : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (row : 2≤charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome+
  value cut.actor.state (update (endGroup group cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup group cut.beforeOutcomes))
 (tailTwo : 2≤energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes) :
 4≤energy state final group outcomes := by
 have prefixNN:=HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 18)
  (NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached) group uniqueGroup inside bounded
 change 0≤energy state cut.middle group cut.beforeOutcomes at prefixNN
 have split:=energy_append state cut.middle final group cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
 have one:=OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
  (endGroup group cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
 change energy cut.middle final (endGroup group cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
  charge NetHack.Soko11Hero315.holeWeight (endGroup group cut.beforeOutcomes) cut.headOutcome+
  value cut.actor.state (update (endGroup group cut.beforeOutcomes) cut.headOutcome)-value cut.middle (endGroup group cut.beforeOutcomes)+
  energy cut.actor.state final (update (endGroup group cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
 have same:=congrArg (energy state final group) cut.outcomesEq
 omega
theorem zero_future_two {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (i : Fin 19) (selected : UpperZero11.locks i⊆group) (hero : state.player∈UpperZero11.region i) :
 2≤energy state final group outcomes := by
 have good : OwnedCorral11.Good UpperZero11.locks UpperZero11.region state (UpperZero11.locks i) := ⟨i,hero,List.Subset.refl _⟩
 have future:=CutEnergy11.future_energy UpperZero11.closed UpperZero11.unique UpperZero11.size
  (by decide) CutEnergy11.upper_paid reached logged completed (UpperZero11.locks i) (UpperZero11.unique i)
  (List.Subset.trans selected inside) (by rw [UpperZero11.size];omega) good
 have bound:=energy_subset reached logged (UpperZero11.locks i) group (UpperZero11.unique i) uniqueGroup selected inside bounded
 omega
#print axioms cut_four
#print axioms zero_future_two
end Owner1007.Q190Upper11
