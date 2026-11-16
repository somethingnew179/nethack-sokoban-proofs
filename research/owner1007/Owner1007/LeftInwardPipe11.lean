import Owner1007.LeftInwardPipe11Node0
import Owner1007.LeftInwardPipe11Node1
import Owner1007.LeftInwardPipe11Node2
import Owner1007.LeftInwardPipe11Node3
import Owner1007.LeftInwardPipe11Node4
import Owner1007.LeftInwardPipe11Node5
import Owner1007.LeftInwardPipe11Proof
namespace Owner1007.LeftInwardPipe11
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting Owner1007.Hero315Frame11 Owner1007.UpperFirstCut11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem closed : PricedCorral11.ClosedExcept soko1_1.board soko1_1.initial.holes locks region paid := by
 apply FastCorral11.closed_of_checks _ _ _ _ _ ZeroWord11.reverse_checked floor
 intro i
 obtain ⟨i,bound⟩:=i
 have cases : i=0∨i=1∨i=2∨i=3∨i=4∨i=5 := by omega
 rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
 ·exact node0
 ·exact node1
 ·exact node2
 ·exact node3
 ·exact node4
 ·exact node5

theorem future_four
 {state final : State} {history dirs : List Dir} {past pastMoves pushes moves : Nat} {outcomes : List Outcome}
 (reached : Trace soko1_1.board soko1_1.initial history state past pastMoves)
 (logged : Logged soko1_1.board state dirs final pushes moves outcomes)
 (group : List Cell) (uniqueGroup : group.Nodup) (inside : group⊆state.boulders)
 (bounded : group.length≤18) (good : OwnedCorral11.Good locks region state group)
 (gone : endGroup group outcomes=[]) : 4≤energy state final group outcomes :=
 future_four_with closed reached logged group uniqueGroup inside bounded good gone
#print axioms closed
#print axioms future_four
end Owner1007.LeftInwardPipe11
