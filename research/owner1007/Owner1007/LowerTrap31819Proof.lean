import Owner1007.LowerTrap31819Data
import Owner1007.LowerTrap31911Proof
namespace Owner1007.LowerTrap31819
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem future_two (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 {prior state dirs final pushes moves outcomes priorPushes priorMoves}
 (reached : Trace soko1_1.board soko1_1.initial prior state priorPushes priorMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (group : List Cell) (groupUnique : group.Nodup) (inside : group⊆state.boulders) (bounded : group.length≤18)
 (good : OwnedCorral11.Good locks region state group) :
 2≤energy state final group outcomes := by
 by_cases enough : 2≤energy state final group outcomes
 · exact enough
 · have cheap : energy state final group outcomes<2 := by omega
   have valid := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant reached
   have retained := OwnedCorralAny11.small_energy_good closed unique (groupCertificate 18) 2
     (fun state dir t outcome group valid unique inside _ head effect pays=>
       LowerTrap31911.exit_row valid unique inside head effect pays)
     logged valid group groupUnique inside bounded good reached.holes_sublist.subset cheap
   obtain ⟨i,_,locksInside⟩ := retained
   have finalSelected := logged.end_subset valid.1 group groupUnique inside
   have card := List.Nodup.length_le_of_subset (unique i) (List.Subset.trans locksInside finalSelected.2)
   have conservation := (reached.append logged.trace).conservation
   have empty : final.holes=[] := completed
   rw [empty] at conservation
   change 18+0=final.boulders.length+16 at conservation
   rw [size i] at card
   omega
theorem rest_positive (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 {beforeDirs state beforePushes beforeMoves before afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (last : Logged soko1_1.board state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (good : OwnedCorral11.Good locks region state (endGroup UpperBudget11.Rest before)) :
 2≤energy soko1_1.initial final UpperBudget11.Rest (before++after) := by
 have selected := first.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 have bound := endGroup_length_le UpperBudget11.Rest before
 have future := future_two closed first.trace last completed _ selected.1 selected.2 (by change (endGroup UpperBudget11.Rest before).length≤18; change (endGroup UpperBudget11.Rest before).length≤10 at bound;omega) good
 have prefixNN := energy_nonnegative first UpperBudget11.Rest (by decide) (by decide)
 have split := energy_append soko1_1.initial state final UpperBudget11.Rest before after
 omega

#print axioms rest_positive
end Owner1007.LowerTrap31819
