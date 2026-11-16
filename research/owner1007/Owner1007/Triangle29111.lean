import Owner1007.Triangle29111Geometry
import Owner1007.Triangle29111Prices
import NetHack.Sokoban.Reduction
namespace Owner1007.Triangle29111
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem barrier_price {prior state dirs final pushes moves outcomes priorPushes priorMoves}
 (reached : Trace soko1_1.board soko1_1.initial prior state priorPushes priorMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (inside : sources⊆state.boulders)
 (good : OwnedCorral11.Good locks region state sources)
 (consumed : endGroup sources outcomes=[]) :
 2≤energy state final [264] outcomes ∨
 2≤energy state final [266] outcomes ∨
 20≤energy state final [291] outcomes := by
 have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
 have holesInside := reached.holes_sublist.subset
 rcases UpperFirstCut11.first_cut_or_quiet (paid:=paid) logged sources with found|quiet
 · obtain ⟨cut⟩ := found
   obtain ⟨source,owner,metadata,pays⟩ := cut.headPaid
   have known := paid_source pays
   have fixed := quiet_fixed cut.before valid.1 inside good holesInside source known
   have currentReached := reached.append cut.before.logged.trace
   have currentValid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant currentReached
   have singletonInside : [source]⊆state.boulders := by simpa using inside known
   have selected := cut.before.logged.end_subset valid.1 [source] (by simp) singletonInside
   have currentRow := exit_row currentValid selected.1 selected.2 cut.headChecked cut.headEffect
     (by rw [fixed];simp) metadata pays
   have prefixNN := HeroLedger.Logged.energy_nonnegative cut.before.logged (groupCertificate 1)
     valid [source] (by simp) singletonInside (by simp)
   change 0≤energy state cut.middle [source] cut.beforeOutcomes at prefixNN
   have actual := step_boulders_nodup _ _ _ _ currentValid.1 cut.headChecked
   have nextUnique := GhostSubset.update_unique _ _ _ cut.headEffect actual _ selected.1 selected.2
   have nextInside := GhostSubset.update_subset _ _ _ cut.headEffect _ selected.1 selected.2
   have selectedBound := endGroup_length_le [source] cut.beforeOutcomes
   have nextBound := update_length (endGroup [source] cut.beforeOutcomes) cut.headOutcome
   have afterValid := (groupCertificate 1).preserved _ _ _ currentValid cut.headChecked
   have suffixNN := HeroLedger.Logged.energy_nonnegative cut.after (groupCertificate 1)
     afterValid _ nextUnique nextInside (by simpa using Nat.le_trans nextBound selectedBound)
   change 0≤energy cut.actor.state final (update (endGroup [source] cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at suffixNN
   have split := energy_append state cut.middle final [source] cut.beforeOutcomes (cut.headOutcome::cut.afterOutcomes)
   have one := OwnedCorral11.energy_cons value NetHack.Soko11Hero315.holeWeight cut.middle cut.actor.state final
     (endGroup [source] cut.beforeOutcomes) cut.headOutcome cut.afterOutcomes
   change energy cut.middle final (endGroup [source] cut.beforeOutcomes) (cut.headOutcome::cut.afterOutcomes)=
     charge NetHack.Soko11Hero315.holeWeight (endGroup [source] cut.beforeOutcomes) cut.headOutcome+
       value cut.actor.state (update (endGroup [source] cut.beforeOutcomes) cut.headOutcome)-
       value cut.middle (endGroup [source] cut.beforeOutcomes)+
       energy cut.actor.state final (update (endGroup [source] cut.beforeOutcomes) cut.headOutcome) cut.afterOutcomes at one
   have bound : threshold source≤energy state final [source] outcomes := by
     rw [cut.outcomesEq]
     omega
   rcases pays with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩
   · exact Or.inl bound
   · exact Or.inr (Or.inl bound)
   · exact Or.inr (Or.inr bound)
 · have endGood := PairFirstCut11.quiet_good closed unique size quiet valid.1 (by decide)
     inside (by decide) good holesInside
   obtain ⟨i,_,locksInside⟩ := endGood
   have retained : 264∈endGroup sources outcomes := locksInside (by simp [locks])
   simpa only [consumed,List.not_mem_nil] using retained
#print axioms barrier_price


end Owner1007.Triangle29111
