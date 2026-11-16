import Owner1007.Left212Word11
import Owner1007.QuietFromCount11
import Owner1007.NoTopBefore187Color11
namespace Owner1007.Left212AtFirst18711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem at_first {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325)
 (cut : FirstCut FirstRest18711.paid soko1_1.initial UpperBudget11.Rest dirs final pushes moves outcomes)
 (northZero : PaidCount11.count FirstRest18711.paid [212] cut.beforeDirs cut.beforeOutcomes=0)
 (cheap212 : energy soko1_1.initial final [212] outcomes<2) :
 endGroup [212] cut.beforeOutcomes=[212] := by
 have downTop := NoTopDown265Before18711.before_first logged completed cheap cut
 have quietDownTop := QuietFromCount11.from_count cut.before.logged Gate265Transport11.upperOrigins downTop
 have quietDown212 := TransportQuiet11.Quiet.project quietDownTop (by decide) (by decide) (by decide)
   [212] (by decide) (by decide)
 have down212 := FirstRest18711.quiet_count_zero quietDown212
 have quietEarly := QuietFromCount11.from_two_counts cut.before.logged [212] northZero down212
 have exactQuiet : UpperQuiet11.Quiet Left212Word11.early soko1_1.initial [212]
     cut.beforeDirs cut.middle cut.beforePushes cut.beforeMoves cut.beforeOutcomes := quietEarly
 let suffix := Logged.cons cut.headChecked cut.headEffect cut.after
 have prefixBound := prefix_energy_le cut.before.logged suffix [212] (by decide) (by decide)
 have prefixCheap : energy soko1_1.initial cut.middle [212] cut.beforeOutcomes<2 := by
   rw [←cut.outcomesEq] at prefixBound
   omega
 obtain ⟨dest,member,tag⟩ := Left212Word11.guard_logged exactQuiet
   NetHack.SokobanLinearPhases.Map11.initial_good (by decide) (by decide) prefixCheap
 have selected := cut.before.logged.end_subset (by decide) [212] (by decide) (by decide)
 have pairSelected := cut.before.logged.end_subset (by decide) ([212]++UpperBudget11.Rest) (by decide) (by decide)
 have pairPerm := HeroLedger.Logged.end_append_perm cut.before.logged (by decide)
   [212] UpperBudget11.Rest (by decide) (by decide)
 have separate := (List.nodup_append.mp (pairPerm.nodup_iff.mp pairSelected.1)).2.2
 obtain ⟨source,restOwner,metadata,pays⟩ := cut.headPaid
 rcases pays with ⟨rfl,north⟩
 have hero : cut.middle.player=239 := by
  have checked : step soko1_1.board cut.middle .north=some cut.actor := by simpa only [north] using cut.headChecked
  exact ActorPrices11.support_of_check 213 cut.middle.player .north 239 (by decide +kernel)
    (step_player_clear _ _ _ _ checked).1 (PairPost11.source_adjacent checked metadata)
 have noHeroBox : 239∉cut.middle.boulders := by
  have clear := (step_player_clear _ _ _ _ cut.headChecked).2.2.1
  simpa only [hero] using clear
 have included := end_subset_selected cut.before.logged (by decide) [212] Gate265Transport11.upperOrigins
   (by decide) (by decide) (by decide) (by decide)
 have colored := NoTopBefore187Color11.before_first logged completed cheap cut
 have insideUpper : dest∈Gate265Transport11.upper := colored (included (by rw [tag];simp))
 change dest∈([212,213,239,265] : List Cell) at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl|rfl
 ·exact tag
 ·exact False.elim (separate 213 (by rw [tag];simp) 213 restOwner rfl)
 ·exact False.elim (noHeroBox (selected.2 (by rw [tag];simp)))
 ·exact False.elim ((show (265:Cell)∉Gate265Transport11.upper from by decide) insideUpper)
#print axioms at_first
end Owner1007.Left212AtFirst18711
