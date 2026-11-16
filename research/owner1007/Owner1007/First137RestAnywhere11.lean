import Owner1007.First137Rest11
import Owner1007.LoggedAppend11
namespace Owner1007.First137RestAnywhere11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
theorem rest_two {beforeDirs state beforePushes beforeMoves before t afterDirs final afterPushes afterMoves after}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 137 (.stay 136)))
 (last : Logged soko1_1.board t.state afterDirs final afterPushes afterMoves after) (completed : Goal final)
 (stationary : ownPushes [137] before=0) :
 2≤energy soko1_1.initial final UpperBudget11.Rest (before++.push 137 (.stay 136)::after) := by
 let logged := first.append (Logged.cons head effect last)
 by_cases enough : 2≤energy soko1_1.initial final UpperBudget11.Rest (before++.push 137 (.stay 136)::after)
 · exact enough
 · have cheapRest : energy soko1_1.initial final UpperBudget11.Rest (before++.push 137 (.stay 136)::after)<2 := by omega
   have compare := energy_subset (Trace.nil soko1_1.initial) logged [135] UpperBudget11.Rest
     (by decide) (by decide) (by decide) (by decide) (by decide)
   have prefixBound := prefix_energy_le first (Logged.cons head effect last) [135] (by decide) (by decide)
   have cheap135 : energy soko1_1.initial state [135] before<2 := by
     change energy soko1_1.initial final [135] (before++.push 137 (.stay 136)::after)≤energy soko1_1.initial final UpperBudget11.Rest (before++.push 137 (.stay 136)::after) at compare
     omega
   obtain ⟨next,member,group⟩ := StationaryGuards11.guard_logged First137Rest11.guards135 first
     NetHack.SokobanLinearPhases.Map11.initial_good (by decide) (by decide) (by simp) stationary cheap135
   have no136 : 136∉state.boulders := by
     obtain ⟨result,_,push⟩ := effect_push_data head effect
     obtain ⟨dest,next,_,_,clear⟩ := (push_first_clear _ _ _ _ _ push).2
     have adjacent : advance soko1_1.board 137 .west=some 136 := by decide +kernel
     have same : dest=136 := Option.some.inj (next.symm.trans adjacent)
     exact same ▸ clear
   have tag135 : endGroup [135] before=[135] := by
     rcases List.mem_cons.mp member with rfl|later
     · exact group
     · have same : next=136 := by simpa only [List.mem_singleton] using later
       have selected := first.end_subset (by decide) [135] (by decide) (by decide)
       exact False.elim (no136 (selected.2 (by rw [group,same];simp)))
   have selected := first.end_subset (by decide) [135] (by decide) (by decide)
   have present : 135∈state.boulders := selected.2 (by rw [tag135];simp)
   have inside : [135,136]⊆t.state.boulders := by
     rw [effect.2]
     intro c member
     simp only [List.mem_cons,List.not_mem_nil,or_false] at member
     rcases member with rfl|rfl
     · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :135≠137)).mpr present)
     · exact List.mem_cons_self
   have tailTag := locked_identity last First137Rest11.frozen inside (by decide :135∈([135,136] : List Cell))
   have globalTag : endGroup [135] (before++.push 137 (.stay 136)::after)=[135] := by
     rw [endGroup_append,tag135]
     simpa only [endGroup,update,move,if_neg (by decide :137∉([135] : List Cell))] using tailTag
   have survives : endGroup [135] (before++.push 137 (.stay 136)::after)≠[] := by rw [globalTag];simp
   have ledger := survivor_energy logged completed 135 survives
   have debt : value soko1_1.initial [135]≤-7 := by decide +kernel
   have nonnegative : (0:Int)≤Int.ofNat (ownPushes [135] (before++.push 137 (.stay 136)::after)) := Int.ofNat_nonneg _
   change energy soko1_1.initial final [135] (before++.push 137 (.stay 136)::after)≤energy soko1_1.initial final UpperBudget11.Rest (before++.push 137 (.stay 136)::after) at compare
   omega
#print axioms rest_two
end Owner1007.First137RestAnywhere11
