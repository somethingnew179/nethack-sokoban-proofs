import Owner1007.UpperResetBudget11
import Owner1007.OneMoveGuards11
namespace Owner1007.UpperResetGuards11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.UpperBudget11

theorem prefix_two {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (i : Fin 2) (sourceEq : cut.actor.pushSource=some (UpperResetBudget11.source i))
 (directionEq : cut.direction=.east)
 (effect : Matches cut.middle cut.actor (.push (UpperResetBudget11.source i) (.stay (UpperResetBudget11.landing i))))
 (cheap : energy soko1_1.initial final U6 outcomes<6) (cell : Cell) (member : cell∈C) :
 energy soko1_1.initial cut.middle [cell] cut.beforeOutcomes<2 := by
 have finalCheap := UpperResetBudget11.cheap_c_two logged completed cut i sourceEq directionEq effect cheap cell member
 have all : C⊆soko1_1.initial.boulders := by decide
 have subset : [cell]⊆soko1_1.initial.boulders := by
   intro c found
   have same : c=cell := List.mem_singleton.mp found
   exact same ▸ all member
 have bound := prefix_energy_le cut.before.logged (Logged.cons cut.headChecked cut.headEffect cut.after)
   [cell] (by simp) subset
 rw [←cut.outcomesEq] at bound
 omega
#print axioms prefix_two

theorem before141_reset {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 138) (directionEq : cut.direction=.east)
 (effect : Matches cut.middle cut.actor (.push 138 (.stay 139)))
 (cheap : energy soko1_1.initial final U6 outcomes<6) :
 endGroup [141] cut.beforeOutcomes=[141] ∨ endGroup [141] cut.beforeOutcomes=[140] := by
 have cheap137 := UpperResetBudget11.cheap_c_two logged completed cut 0 sourceEq directionEq effect cheap 137 (by decide)
 have history := UpperResetHistory11.before138east cut sourceEq directionEq effect cheap137
 have prefixCheap := prefix_two logged completed cut 0 sourceEq directionEq effect cheap 141 (by decide)
 obtain ⟨next,member,tag⟩ := OneMoveGuards11.guard141_one cut.before.logged history.1 history.2 prefixCheap
 have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
 obtain ⟨result,_,push⟩ := effect_push_data checked effect
 obtain ⟨landing,adjacent,_,_,clear⟩ := (push_first_clear soko1_1.board cut.middle 138 .east result push).2
 have landingEq : landing=139 := Option.some.inj (adjacent.symm.trans (by decide))
 have noLanding : 139∉cut.middle.boulders := landingEq ▸ clear
 have before := cut.before.logged.end_subset (by decide) [141] (by decide) (by decide)
 change next∈([141,140,139] : List Cell) at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl
 · exact Or.inl tag
 · exact Or.inr tag
 · exact False.elim (noLanding (before.2 (by rw [tag]; simp)))
#print axioms before141_reset

theorem before193_reset {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final)
 (cut : FirstCut UpperZero11.paid soko1_1.initial originalGroup dirs final pushes moves outcomes)
 (sourceEq : cut.actor.pushSource=some 190) (directionEq : cut.direction=.east)
 (effect : Matches cut.middle cut.actor (.push 190 (.stay 191)))
 (cheap : energy soko1_1.initial final U6 outcomes<6) :
 endGroup [193] cut.beforeOutcomes=[193] ∨ endGroup [193] cut.beforeOutcomes=[192] := by
 have cheap137 := UpperResetBudget11.cheap_c_two logged completed cut 1 sourceEq directionEq effect cheap 137 (by decide)
 have history := UpperResetHistory11.before190east cut sourceEq directionEq effect cheap137
 have prefixCheap := prefix_two logged completed cut 1 sourceEq directionEq effect cheap 193 (by decide)
 obtain ⟨next,member,tag⟩ := OneMoveGuards11.guard193_one cut.before.logged history.1 history.2 prefixCheap
 have checked : step soko1_1.board cut.middle .east=some cut.actor := by simpa only [directionEq] using cut.headChecked
 obtain ⟨result,_,push⟩ := effect_push_data checked effect
 obtain ⟨landing,adjacent,_,_,clear⟩ := (push_first_clear soko1_1.board cut.middle 190 .east result push).2
 have landingEq : landing=191 := Option.some.inj (adjacent.symm.trans (by decide))
 have noLanding : 191∉cut.middle.boulders := landingEq ▸ clear
 have before := cut.before.logged.end_subset (by decide) [193] (by decide) (by decide)
 change next∈([193,192,191] : List Cell) at member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl|rfl|rfl
 · exact Or.inl tag
 · exact Or.inr tag
 · exact False.elim (noLanding (before.2 (by rw [tag]; simp)))
#print axioms before193_reset
end Owner1007.UpperResetGuards11
