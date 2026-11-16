import Owner1007.LeftInwardStart11Node0
import Owner1007.LeftInwardStart11Node1
import Owner1007.LeftInwardStart11Proof
import Owner1007.LeftInwardPipe11
namespace Owner1007.LeftInwardStart11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1 := by omega
 rcases cases with rfl|rfl
 ·exact node0
 ·exact node1

theorem future_four
 {state final : State} {beforeDirs dirs : List Dir} {beforePushes beforeMoves pushes moves : Nat} {before outcomes : List Outcome}
 (first : Logged soko1_1.board soko1_1.initial beforeDirs state beforePushes beforeMoves before)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes) (completed : Goal final)
 (upperCap : energy soko1_1.initial final UpperBudget11.U6 (before++outcomes)≤8)
 (restCap : energy soko1_1.initial final UpperBudget11.Rest (before++outcomes)<2)
 (i : Fin 2) (stationary : ownPushes [other i] before=0)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (same : group.Perm (locks i)) (hero : state.player∈region i)
 (gone : endGroup group outcomes=[]) : 4≤energy state final group outcomes :=
 future_four_with closed LeftInwardPipe11.closed first logged completed upperCap restCap i stationary group uniqueGroup inside same hero gone
#print axioms closed
#print axioms future_four
end Owner1007.LeftInwardStart11
