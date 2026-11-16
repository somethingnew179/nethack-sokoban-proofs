import Owner1007.CentralFirst11Geometry
import Owner1007.LowerTrap31819Geometry
import Owner1007.LowerElevator11Geometry
import Owner1007.Shaft18711Geometry
import Owner1007.TightSurvivors11
import Owner1007.CoreStart11
import Owner1007.ElevatorAdvance11
import Owner1007.ShaftArrival18711
namespace Owner1007.CanonicalArrival18711
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11

structure Arrival (dirs : List Dir) (final : State) (pushes moves : Nat) (outcomes : List Outcome) where
 middle : State
 actor : Transition
 beforeDirs : List Dir
 beforePushes : Nat
 beforeMoves : Nat
 beforeOutcomes : List Outcome
 afterDirs : List Dir
 afterPushes : Nat
 afterMoves : Nat
 afterOutcomes : List Outcome
 first : Logged soko1_1.board soko1_1.initial beforeDirs middle beforePushes beforeMoves beforeOutcomes
 head : step soko1_1.board middle .north=some actor
 effect : Matches middle actor (.push 213 (.stay 187))
 last : Logged soko1_1.board actor.state afterDirs final afterPushes afterMoves afterOutcomes
 dirsEq : dirs=beforeDirs++.north::afterDirs
 outcomesEq : outcomes=beforeOutcomes++.push 213 (.stay 187)::afterOutcomes
 pushesEq : pushes=beforePushes+1+afterPushes
 movesEq : moves=beforeMoves+1+afterMoves
 owner : 213∈endGroup UpperBudget11.Rest beforeOutcomes
 selected : ([187,266] : List Cell)⊆update (endGroup UpperBudget11.Rest beforeOutcomes) (.push 213 (.stay 187))

theorem arrival
 (centralClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes CentralFirst11.locks CentralFirst11.region CentralFirst11.paid)
 (trapClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes LowerTrap31819.locks LowerTrap31819.region LowerTrap31819.paid)
 (elevatorClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes LowerElevator11.locks LowerElevator11.region LowerElevator11.paid)
 (shaftClosed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes Shaft18711.locks Shaft18711.region Shaft18711.paid)
 {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes) (completed : Goal final) (cheap : pushes≤325) :
 Nonempty (Arrival dirs final pushes moves outcomes) := by
 obtain ⟨_,_,_,zeroRest⟩ := Tight32511.budgets logged completed cheap
 have stationary321 := (TightSurvivors11.stationary_zero_survivors logged completed cheap).2
 obtain ⟨central⟩ := CentralFirst11.first_cut centralClosed logged completed
 obtain ⟨centralHead,centralHero,centralSubset,centralGood,centralZero,central317⟩ :=
   CoreStart11.start centralClosed trapClosed logged completed zeroRest stationary321 central
 let toC := CoreStart11.toState central
 have currentRest := toC.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 have groupInside := List.Subset.trans centralSubset currentRest.2
 obtain ⟨elevator⟩ := LowerElevator11.first_cut elevatorClosed toC.trace central.after completed CoreStart11.G
   (by decide) groupInside (by decide) centralGood
 have zeroWholeC : energy soko1_1.initial final UpperBudget11.Rest
     (CoreStart11.prefixOutcomes central++central.afterOutcomes)=0 := by
   rw [CoreStart11.effects central]
   exact zeroRest
 obtain ⟨elevatorHead,elevatorHero,pairSubset,pairZero,pairActive,pairGood,_⟩ :=
   ElevatorAdvance11.start elevatorClosed toC central.after zeroWholeC centralSubset centralGood elevator
 let toE := RestCutAdvance11.afterLog toC elevator
 have effectsE : RestCutAdvance11.afterPrefix toC elevator++elevator.afterOutcomes=outcomes := by
   have joined := RestCutAdvance11.effects toC elevator
   change RestCutAdvance11.afterPrefix toC elevator++elevator.afterOutcomes=
     CoreStart11.prefixOutcomes central++central.afterOutcomes at joined
   exact joined.trans (CoreStart11.effects central)
 have zeroWholeE : energy soko1_1.initial final UpperBudget11.Rest
     (RestCutAdvance11.afterPrefix toC elevator++elevator.afterOutcomes)=0 := by rw [effectsE];exact zeroRest
 obtain ⟨shaft,shaftHead,shaftHero,shaftSubset,shaftZero⟩ :=
   ShaftArrival18711.arrival shaftClosed toE elevator.after completed zeroWholeE pairSubset pairActive elevatorHero
 have restAtE := toE.end_subset (by decide) UpperBudget11.Rest (by decide) (by decide)
 have pairInside := List.Subset.trans pairSubset restAtE.2
 obtain ⟨_,north,_,_⟩ := Shaft18711.useful shaftClosed toE.trace [265,266] (by decide)
   pairInside (by decide) pairGood pairZero shaft
 let beforeLog := toE.append shaft.before.logged
 let beforeOutcomes := RestCutAdvance11.afterPrefix toC elevator++shaft.beforeOutcomes
 have effect : Matches shaft.middle shaft.actor (.push 213 (.stay 187)) := by simpa only [shaftHead] using shaft.headEffect
 have metadata : shaft.actor.pushSource=some 213 := by rw [effect.2]
 obtain ⟨source,owner,record,_⟩ := shaft.headPaid
 have same : source=213 := Option.some.inj (record.symm.trans metadata)
 have owner213 : 213∈endGroup [265,266] shaft.beforeOutcomes := same ▸ owner
 have validE := NetHack.SokobanLinearPhases.Map11.trace_phase_invariant toE.trace
 have inclusion := end_subset_selected shaft.before.logged validE.1 [265,266]
   (endGroup UpperBudget11.Rest (RestCutAdvance11.afterPrefix toC elevator))
   (by decide) restAtE.1 pairSubset restAtE.2
 have originalOwner : 213∈endGroup UpperBudget11.Rest beforeOutcomes := by
   unfold beforeOutcomes
   rw [endGroup_append]
   exact inclusion owner213
 have selected : ([187,266] : List Cell)⊆update (endGroup UpperBudget11.Rest beforeOutcomes) (.push 213 (.stay 187)) := by
   intro c member
   have afterMember := shaftSubset member
   have joined : RestCutAdvance11.afterPrefix toE shaft=beforeOutcomes++[.push 213 (.stay 187)] := by
     change RestCutAdvance11.afterPrefix toC elevator++(shaft.beforeOutcomes++[shaft.headOutcome])=
       (RestCutAdvance11.afterPrefix toC elevator++shaft.beforeOutcomes)++[.push 213 (.stay 187)]
     rw [shaftHead]
     simp only [List.append_assoc]
   rw [joined,endGroup_append] at afterMember
   exact afterMember
 have shaftCost : shaft.actor.pushCost=1 := by rw [effect.2];rfl
 refine ⟨{
   middle:=shaft.middle, actor:=shaft.actor,
   beforeDirs:=(central.beforeDirs++[central.direction])++(elevator.beforeDirs++[elevator.direction])++shaft.beforeDirs,
   beforePushes:=(central.beforePushes+central.actor.pushCost)+(elevator.beforePushes+elevator.actor.pushCost)+shaft.beforePushes,
   beforeMoves:=(central.beforeMoves+1)+(elevator.beforeMoves+1)+shaft.beforeMoves,
   beforeOutcomes:=beforeOutcomes, afterDirs:=shaft.afterDirs,
   afterPushes:=shaft.afterPushes, afterMoves:=shaft.afterMoves, afterOutcomes:=shaft.afterOutcomes,
   first:=beforeLog, head:=(by simpa only [north] using shaft.headChecked), effect:=effect, last:=shaft.after,
   dirsEq:=?_, outcomesEq:=?_, pushesEq:=?_, movesEq:=?_, owner:=originalOwner, selected:=selected
 }⟩
 · calc
     dirs=central.beforeDirs++central.direction::central.afterDirs := central.dirsEq
     _=central.beforeDirs++central.direction::(elevator.beforeDirs++elevator.direction::elevator.afterDirs) :=
       congrArg (fun rest=>central.beforeDirs++central.direction::rest) elevator.dirsEq
     _=central.beforeDirs++central.direction::(elevator.beforeDirs++elevator.direction::(shaft.beforeDirs++shaft.direction::shaft.afterDirs)) :=
       congrArg (fun rest=>central.beforeDirs++central.direction::(elevator.beforeDirs++elevator.direction::rest)) shaft.dirsEq
     _=_ := by simp only [List.append_assoc,List.cons_append,List.nil_append,north]
 · have joined := RestCutAdvance11.effects toE shaft
   change RestCutAdvance11.afterPrefix toE shaft++shaft.afterOutcomes=
     RestCutAdvance11.afterPrefix toC elevator++elevator.afterOutcomes at joined
   have allEffects := joined.trans effectsE
   have shape : RestCutAdvance11.afterPrefix toE shaft=beforeOutcomes++[.push 213 (.stay 187)] := by
     change RestCutAdvance11.afterPrefix toC elevator++(shaft.beforeOutcomes++[shaft.headOutcome])=
       (RestCutAdvance11.afterPrefix toC elevator++shaft.beforeOutcomes)++[.push 213 (.stay 187)]
     rw [shaftHead]
     simp only [List.append_assoc]
   rw [shape] at allEffects
   simpa only [List.append_assoc,List.cons_append,List.nil_append] using allEffects.symm
 · have c:=central.pushesEq
   have e:=elevator.pushesEq
   have s:=shaft.pushesEq
   omega
 · have c:=central.movesEq
   have e:=elevator.movesEq
   have s:=shaft.movesEq
   omega
theorem canonical {dirs final pushes moves outcomes}
 (logged : Logged soko1_1.board soko1_1.initial dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : pushes≤325) :
 Nonempty (Arrival dirs final pushes moves outcomes) :=
 arrival CentralFirst11.closed LowerTrap31819.closed LowerElevator11.closed Shaft18711.closed logged completed cheap
#print axioms arrival
#print axioms canonical
end Owner1007.CanonicalArrival18711