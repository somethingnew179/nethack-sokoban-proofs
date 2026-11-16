import Owner1007.BeforeCentral31711
import Owner1007.ZeroRestTail11
import Owner1007.LowerElevator11Data
namespace Owner1007.CoreStart11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
def G : List Cell := [266,292,317]
def prefixOutcomes {dirs final pushes moves outcomes}
 (cut : FirstCut CentralFirst11.paid soko1_1.initial CentralFirst11.sources dirs final pushes moves outcomes) : List Outcome :=
 cut.beforeOutcomes++[cut.headOutcome]
def headLog {dirs final pushes moves outcomes}
 (cut : FirstCut CentralFirst11.paid soko1_1.initial CentralFirst11.sources dirs final pushes moves outcomes) :
 Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
 .cons cut.headChecked cut.headEffect (.nil _)
def toState {dirs final pushes moves outcomes}
 (cut : FirstCut CentralFirst11.paid soko1_1.initial CentralFirst11.sources dirs final pushes moves outcomes) :=
 cut.before.logged.append (headLog cut)
theorem effects {dirs final pushes moves outcomes}
 (cut : FirstCut CentralFirst11.paid soko1_1.initial CentralFirst11.sources dirs final pushes moves outcomes) :
 prefixOutcomes cut++cut.afterOutcomes=outcomes := by
 simpa only [prefixOutcomes,List.append_assoc,List.cons_append,List.nil_append] using cut.outcomesEq.symm

theorem start
 (centralClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes CentralFirst11.locks CentralFirst11.region CentralFirst11.paid)
 (trapClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes LowerTrap31819.locks LowerTrap31819.region LowerTrap31819.paid)
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (zeroRest : energy soko1_1.initial final UpperBudget11.Rest outcomes=0)
 (stationary321 : ownPushes [321] outcomes=0)
 (cut : FirstCut CentralFirst11.paid soko1_1.initial CentralFirst11.sources dirs final pushes moves outcomes) :
 cut.headOutcome=.push 293 (.stay 292) ∧cut.actor.state.player=293 ∧
 G⊆endGroup UpperBudget11.Rest (prefixOutcomes cut) ∧
 OwnedCorral11.Good LowerElevator11.locks LowerElevator11.region cut.actor.state G ∧
 energy cut.actor.state final G cut.afterOutcomes=0 ∧
 ownPushes [317] (prefixOutcomes cut)=0 := by
 obtain ⟨sourceEq,directionEq,headEq⟩ := CentralFirst11.first_west centralClosed logged completed zeroRest cut
 have stationary317 := BeforeCentral31711.stationary_before centralClosed trapClosed logged completed zeroRest stationary321 cut
 have effect : Matches cut.middle cut.actor (.push 293 (.stay 292)) := by simpa only [headEq] using cut.headEffect
 have beforeZero (cell : Cell) (member : cell∈([266,293,317] : List Cell)) : ownPushes [cell] cut.beforeOutcomes=0 := by
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl
   · exact cut.before.fixed (by decide :266∈CentralFirst11.sources) (fun _=>(show 266∈CentralFirst11.sources from by decide))
   · exact cut.before.fixed (by decide :293∈CentralFirst11.sources) (fun _=>(show 293∈CentralFirst11.sources from by decide))
   · exact stationary317
 have beforeMember (cell : Cell) (member : cell∈([266,293,317] : List Cell)) :
     cell∈endGroup UpperBudget11.Rest cut.beforeOutcomes := by
   have tag : endGroup [cell] cut.beforeOutcomes=[cell] := no_push_unchanged _ _ (beforeZero cell member)
   have sourceRest : cell∈UpperBudget11.Rest := (show ([266,293,317] : List Cell)⊆UpperBudget11.Rest from by decide) member
   have subset : [cell]⊆UpperBudget11.Rest := by simpa using sourceRest
   have included := end_subset_selected cut.before.logged (by decide) [cell] UpperBudget11.Rest
     (by simp) (by decide) subset (by decide)
   exact included (by rw [tag];simp)
 have selectedG : G⊆endGroup UpperBudget11.Rest (prefixOutcomes cut) := by
   intro c member
   simp only [G,List.mem_cons,List.not_mem_nil,or_false] at member
   unfold prefixOutcomes
   rw [endGroup_append]
   change c∈update (endGroup UpperBudget11.Rest cut.beforeOutcomes) cut.headOutcome
   rw [headEq]
   simp only [update,move,if_pos (beforeMember 293 (by decide)),post]
   rcases member with rfl|rfl|rfl
   · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :266≠293)).mpr (beforeMember 266 (by decide)))
   · exact List.mem_cons_self
   · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :317≠293)).mpr (beforeMember 317 (by decide)))
 have hero : cut.actor.state.player=293 := by rw [effect.2]
 have good : OwnedCorral11.Good LowerElevator11.locks LowerElevator11.region cut.actor.state G := by
   refine ⟨⟨0,by decide⟩,?_,?_⟩
   · rw [hero];decide +kernel
   · change ([266,292,317] : List Cell)⊆G
     exact List.Subset.refl _
 have zero : energy cut.actor.state final G cut.afterOutcomes=0 := by
   apply ZeroRestTail11.subset_zero (toState cut) cut.after _ G (by decide) selectedG
   change energy soko1_1.initial final UpperBudget11.Rest (prefixOutcomes cut++cut.afterOutcomes)=0
   rw [effects cut]
   exact zeroRest
 have fixed317 : ownPushes [317] (prefixOutcomes cut)=0 := by
   unfold prefixOutcomes
   rw [ownPushes_append,no_push_unchanged _ _ stationary317,headEq]
   simpa only [ownPushes,ownPush,if_neg (by decide :293∉([317] : List Cell)),Nat.zero_add,Nat.add_zero] using stationary317
 exact ⟨headEq,hero,selectedG,good,zero,fixed317⟩
#print axioms start
end Owner1007.CoreStart11
