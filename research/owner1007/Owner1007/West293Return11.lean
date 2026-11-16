import Owner1007.ZeroEnergySlice11
import Owner1007.OtherElevatorNoAbove11
import Owner1007.ModeC264Mass11
namespace Owner1007.West293Return11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11
open Owner1007.ModeC264Mass11 (Other)
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem impossible {beforeDirs state beforePushes beforeMoves before t dirs middle pushes moves outcomes lastDirs final lastPushes lastMoves last}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (head : step soko1_1.board state .west=some t) (effect : Matches state t (.push 293 (.stay 292)))
 (logged : Logged soko1_1.board t.state dirs middle pushes moves outcomes)
 (suffix : Logged soko1_1.board middle lastDirs final lastPushes lastMoves last)
 (zero : energy soko1_1.initial final Other (before++.push 293 (.stay 292)::(outcomes++last))=0)
 (owns : ([266,293,317] : List Cell)⊆endGroup Other before)
 (stationary : ownPushes [266] (before++.push 293 (.stay 292)::outcomes)=0)
 (hero : middle.player=213) : False := by
 let one : Logged soko1_1.board state [.west] t.state t.pushCost 1 [.push 293 (.stay 292)] := .cons head effect (.nil _)
 let toAfter := first.append one
 let effects := before++[.push 293 (.stay 292)]
 have owner293 : 293∈endGroup Other before := owns (by decide)
 have selected : ([266,292,317] : List Cell)⊆endGroup Other effects := by
  change ([266,292,317] : List Cell)⊆endGroup Other (before++[.push 293 (.stay 292)])
  rw [endGroup_append]
  change ([266,292,317] : List Cell)⊆update (endGroup Other before) (.push 293 (.stay 292))
  simp only [update,move,if_pos owner293,post]
  intro c h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl
  ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :266≠293)).mpr (owns (by decide)))
  ·exact List.mem_cons_self
  ·exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne (by decide :317≠293)).mpr (owns (by decide)))
 have eqEffects : effects++outcomes++last=before++.push 293 (.stay 292)::(outcomes++last) := by
  simp only [effects,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]
 have zeroHere : energy soko1_1.initial final Other (effects++outcomes++last)=0 := by rw [eqEffects];exact zero
 have zeroGroup := ZeroEnergySlice11.subset_zero toAfter logged suffix Other (by decide) (by decide) zeroHere
   [266,292,317] (by decide) selected
 have facts := toAfter.end_subset (by decide) Other (by decide) (by decide)
 have inside := List.Subset.trans selected facts.2
 have good : OwnedCorral11.Good LowerElevator11.locks LowerElevator11.region t.state OtherElevatorNoAbove11.G := by
  refine ⟨0,?_,?_⟩
  ·have same : t.state.player=293 := by rw [effect.2]
   rw [same];decide +kernel
  ·exact List.Subset.refl _
 have beforeZero : ownPushes [266] before=0 := by
  rw [ownPushes_append] at stationary
  omega
 have localZero : ownPushes [266] outcomes=0 := by
  rw [ownPushes_append,no_push_unchanged _ _ beforeZero] at stationary
  simpa only [ownPushes,ownPush,if_neg (by decide :293∉([266] : List Cell)),update,move,beforeZero,Nat.add_zero,Nat.zero_add] using stationary
 exact OtherElevatorNoAbove11.no_upper toAfter.trace logged inside good zeroGroup localZero hero
#print axioms impossible
end Owner1007.West293Return11
