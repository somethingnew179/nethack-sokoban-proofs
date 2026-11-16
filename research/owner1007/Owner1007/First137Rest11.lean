import Owner1007.StationaryGuards11
import Owner1007.UpperSixExit11
import Owner1007.LockedTokens
import Owner1007.HeroEnergyTrace11
namespace Owner1007.First137Rest11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem guards135 : (List.range 16).all (StationaryGuards11.guardCheck 137 [135,136])=true := by decide +kernel
#print axioms guards135

theorem frozen : Owner1007.Locked soko1_1.board [135,136] := Owner1007.locked_of_check _ _ (by decide +kernel)
theorem rest_two {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 137) (directionEq : cut.direction=.west)
 (headEq : cut.headOutcome=.push 137 (.stay 136)) :
 2≤energy soko1_1.initial final UpperBudget11.Rest outcomes := by
 by_cases enough : 2≤energy soko1_1.initial final UpperBudget11.Rest outcomes
 · exact enough
 · have cheapRest : energy soko1_1.initial final UpperBudget11.Rest outcomes<2 := by omega
   have stationary := cut.stationary_source 137 (by decide) sourceEq
   have compare := energy_subset (Trace.nil soko1_1.initial) logged [135] UpperBudget11.Rest
     (by decide) (by decide) (by decide) (by decide) (by decide)
   have prefixBound := prefix_energy_le cut.before.logged (Logged.cons cut.headChecked cut.headEffect cut.after)
     [135] (by decide) (by decide)
   rw [←cut.outcomesEq] at prefixBound
   have cheap135 : energy soko1_1.initial cut.middle [135] cut.beforeOutcomes<2 := by omega
   obtain ⟨next,member,group⟩ := StationaryGuards11.guard_logged guards135 cut.before.logged
     NetHack.SokobanLinearPhases.Map11.initial_good (by decide) (by decide) (by simp) stationary cheap135
   have effect : Matches cut.middle cut.actor (.push 137 (.stay 136)) := by simpa only [headEq] using cut.headEffect
   have no136 : 136∉cut.middle.boulders := by
     obtain ⟨result,_,push⟩ := effect_push_data cut.headChecked effect
     obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear _ _ _ _ _ push).2
     have adjacent : advance soko1_1.board 137 cut.direction=some 136 := by rw [directionEq];decide +kernel
     have same : dest=136 := Option.some.inj (next.symm.trans adjacent)
     exact same ▸ clear
   have tag135 : endGroup [135] cut.beforeOutcomes=[135] := by
     rcases List.mem_cons.mp member with rfl|later
     · exact group
     · have same : next=136 := by simpa only [List.mem_singleton] using later
       have selected := cut.before.logged.end_subset (by decide) [135] (by decide) (by decide)
       have present : 136∈cut.middle.boulders := selected.2 (by rw [group,same];simp)
       exact False.elim (no136 present)
   have selected := cut.before.logged.end_subset (by decide) [135] (by decide) (by decide)
   have present : 135∈cut.middle.boulders := selected.2 (by rw [tag135];simp)
   have inside : [135,136]⊆cut.actor.state.boulders := by
     rw [effect.2]
     intro c member
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl
     · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :135≠137)).mpr present)
     · exact List.mem_cons_self
   have tailTag := locked_identity cut.after frozen inside (by decide :135∈([135,136] : List Cell))
   have globalTag : endGroup [135] outcomes=[135] := by
     rw [cut.outcomesEq,endGroup_append,tag135,headEq]
     simpa only [endGroup,update,move,if_neg (by decide :137∉([135] : List Cell))] using tailTag
   have survives : endGroup [135] outcomes≠[] := by rw [globalTag];simp
   have ledger := survivor_energy logged completed 135 survives
   have debt : value soko1_1.initial [135]≤-7 := by decide +kernel
   have nonnegative : (0:Int)≤Int.ofNat (ownPushes [135] outcomes) := Int.ofNat_nonneg _
   omega
#print axioms rest_two

end Owner1007.First137Rest11