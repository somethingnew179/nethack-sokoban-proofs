import Owner1007.LeftFourLaneLift11
import Owner1007.LeftTwoLaneForward11
namespace Owner1007.LeftFourLaneForward11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
open Owner1007.LeftFourLane11
theorem cases : ∀i : Fin 21,
 (left i=184∧right i=186)∨(left i=184∧right i=187)∨(left i=185∧right i=187)∨
 (left i=184∧right i=185)∨(left i=185∧right i=186)∨(left i=186∧right i=187)∨
 right i=188∨right i=189∨right i=190 := by decide +kernel
theorem frozen184185 {beforeDirs state beforePushes beforeMoves before dirs final pushes moves outcomes}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (tail : Logged soko1_1.board state dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : beforePushes+pushes≤327)
 (physical : [184,185]⊆state.boulders) : False := by
 have persists := Owner1007.locked_trace
  (Owner1007.locked_of_check soko1_1.board [184,185] (by decide +kernel)) tail.trace physical
 have bound := TightRowPairs32711.other_capacity (first.append tail) completed cheap [184,185] (by decide) persists (by decide)
 change 2≤1 at bound
 omega
theorem at_forward
 (closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid)
 (refined : RankedCorral11.Refinement locks region left (fun _=>0) paid)
 {dirs final pushes moves outcomes}
 (cut : FirstCut RightEarlyWords11.paid soko1_1.initial RightEarlyWords11.G dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤327)
 (cheapLeft : energy soko1_1.initial final [186] outcomes≤4)
 (cheapUpper : energy soko1_1.initial final UpperBudget11.U6 outcomes<8)
 (cheapRest : energy soko1_1.initial final UpperBudget11.Rest outcomes<2)
 (source190 : cut.actor.pushSource=some 190) (west : cut.direction=.west)
 (head190 : cut.headOutcome=.push 190 (.stay 189))
 (tag191 : endGroup [191] cut.beforeOutcomes=[190]) :
 (endGroup [186] cut.beforeOutcomes=[184]∧endGroup [188] cut.beforeOutcomes=[186])∨
 (endGroup [186] cut.beforeOutcomes=[184]∧endGroup [188] cut.beforeOutcomes=[187])∨
 (endGroup [186] cut.beforeOutcomes=[185]∧endGroup [188] cut.beforeOutcomes=[187]) := by
 let suffix : Logged soko1_1.board cut.middle (cut.direction::cut.afterDirs) final
  (cut.actor.pushCost+cut.afterPushes) (1+cut.afterMoves) (cut.headOutcome::cut.afterOutcomes) :=
  .cons cut.headChecked cut.headEffect cut.after
 have actorCap : energy soko1_1.initial final [186] (cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)≤4 := by
  rw [←cut.outcomesEq];exact cheapLeft
 have upperCap : energy soko1_1.initial final UpperBudget11.U6 (cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)<8 := by
  rw [←cut.outcomesEq];exact cheapUpper
 have restCap : energy soko1_1.initial final UpperBudget11.Rest (cut.beforeOutcomes++cut.headOutcome::cut.afterOutcomes)<2 := by
  rw [←cut.outcomesEq];exact cheapRest
 obtain ⟨i,tagLeft,tagRight,_⟩:=LeftFourLaneLift11.prefix_word closed refined cut.before suffix completed actorCap upperCap restCap
 have beforeCheap : cut.beforePushes+(cut.actor.pushCost+cut.afterPushes)≤327 := by
  have eq:=cut.pushesEq
  omega
 have physical : locks i⊆cut.middle.boulders := by
  have factsLeft := cut.before.logged.end_subset (by decide) [186] (by decide) (by decide)
  have factsRight := cut.before.logged.end_subset (by decide) [188] (by decide) (by decide)
  intro c member
  change c∈[left i,right i] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl
  ·exact factsLeft.2 (by rw [tagLeft];simp)
  ·exact factsRight.2 (by rw [tagRight];simp)
 have checked : step soko1_1.board cut.middle .west=some cut.actor := by simpa only [west] using cut.headChecked
 have effect : Matches cut.middle cut.actor (.push 190 (.stay 189)) := by simpa only [head190] using cut.headEffect
 rcases cases i with good0|good1|good2|bad0|bad1|bad2|at188|at189|at190
 ·exact Or.inl ⟨by simpa only [good0.1] using tagLeft,by simpa only [good0.2] using tagRight⟩
 ·exact Or.inr (Or.inl ⟨by simpa only [good1.1] using tagLeft,by simpa only [good1.2] using tagRight⟩)
 ·exact Or.inr (Or.inr ⟨by simpa only [good2.1] using tagLeft,by simpa only [good2.2] using tagRight⟩)
 ·have locked : [184,185]⊆cut.middle.boulders := by simpa only [locks,bad0.1,bad0.2] using physical
  exact False.elim (frozen184185 cut.before.logged suffix completed beforeCheap locked)
 ·have locked : [185,186]⊆cut.middle.boulders := by simpa only [locks,bad1.1,bad1.2] using physical
  exact False.elim (LeftTwoLaneForward11.frozen185186 cut.before.logged suffix completed beforeCheap locked)
 ·have locked : TightRowPairs11.pairs 0⊆cut.middle.boulders := by
   change [186,187]⊆cut.middle.boulders
   simpa only [locks,bad2.1,bad2.2] using physical
  exact False.elim (TightRowPairs32711.excluded cut.before.logged suffix completed beforeCheap 0 locked)
 ·have present188 : 188∈cut.middle.boulders := physical (by simp [locks,at188])
  have afterPhysical : TightRowPairs11.pairs 2⊆cut.actor.state.boulders := by
   change [188,189]⊆cut.actor.state.boulders
   rw [effect.2]
   intro c member
   simp only [List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl
   ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :188≠190)).mpr present188)
   ·exact List.mem_cons_self
  let headLogged : Logged soko1_1.board cut.middle [cut.direction] cut.actor.state cut.actor.pushCost 1 [cut.headOutcome] :=
   .cons cut.headChecked cut.headEffect (.nil _)
  have afterCheap : cut.beforePushes+cut.actor.pushCost+cut.afterPushes≤327 := by omega
  exact False.elim (TightRowPairs32711.excluded (cut.before.logged.append headLogged) cut.after completed afterCheap 2 afterPhysical)
 ·have present189 : 189∈cut.middle.boulders := physical (by simp [locks,at189])
  obtain ⟨result,_,push⟩:=effect_push_data checked effect
  obtain ⟨dest,next,_,_,clear⟩:=(push_first_clear _ _ _ _ _ push).2
  have destEq : dest=189 := Option.some.inj (next.symm.trans (show advance soko1_1.board 190 .west=some 189 by decide +kernel))
  exact False.elim (clear (destEq.symm ▸ present189))
 ·have facts := cut.before.logged.end_subset (by decide) [188,191] (by decide) (by decide)
  have split := HeroLedger.Logged.end_append_perm cut.before.logged (by decide) [188] [191] (by decide) (by decide)
  rw [tagRight,at190,tag191] at split
  have unique := split.nodup_iff.mp facts.1
  simpa using unique

#print axioms at_forward
end Owner1007.LeftFourLaneForward11
