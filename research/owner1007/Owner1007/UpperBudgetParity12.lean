import Owner1007.ConsumedParity12
import Owner1007.NorthUpperTwoConsumed12
import Owner1007.NorthWrap12
import Owner1007.Final222
namespace Owner1007.UpperBudgetParity12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential
abbrev U := PreCage12.U
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem all_consumed {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (small : energy p U outcomes<4) : ∀cell∈U,endGroup [cell] outcomes=[] := by
 intro cell member
 by_cases gone : endGroup [cell] outcomes=[]
 ·exact gone
 ·have singleton : [cell]⊆U := by simpa using member
  have inside : U⊆FirstSplit12.afterN.boulders := by decide +kernel
  have mono := logged.energy_mono Generated.soko1_2_potential_valid (by decide +kernel)
    [cell] U (by simp) (by decide +kernel) (List.Subset.trans singleton inside) inside singleton
  change energy p [cell] outcomes≤energy p U outcomes at mono
  have ledger := survivor_energy p cell outcomes gone
  have debts : ∀c∈U,(8:Int)≤-p.boulder c := by decide +kernel
  have high := debts cell member
  have nn := Int.natCast_nonneg (ownPushes [cell] outcomes)
  simp only [Int.ofNat_eq_natCast] at ledger
  omega

theorem end_empty {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (small : energy p U outcomes<4) : endGroup U outcomes=[] := by
 have bound := logged.end_count_le (by decide +kernel) U (by decide +kernel) (by decide +kernel)
   (fun _=>false) (fun cell member _=>all_consumed logged small cell member)
 have empty : U.filter (fun _=>false)=[] := by decide +kernel
 rw [empty] at bound
 simpa only [List.length_nil,Nat.le_zero_eq,List.length_eq_zero_iff] using bound

/-- Raw Upper energy cannot be3: its original five are absorbed and their
checkerboard correction is even. The universal raw Upper reserve is2. -/
theorem two_of_lt_four {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (small : energy p U outcomes<4) : energy p U outcomes=2 := by
 have even := ConsumedParity12.consumed_even NorthBound12.north_reached logged completed
   U (by decide +kernel) (by decide +kernel) (end_empty logged small)
   (ConsumedParity12.left_compatible U (by decide +kernel))
 change (energy p U outcomes)%2=0 at even
 have whole := NorthWrap12.canonical_north logged
 let all := .walk 397::.push 371 (.stay 345)::outcomes
 have bound := Final222.upper_energy_two whole completed
 have same := NorthWrap12.energy_north U outcomes
 have updated : update U (.push 371 (.stay 345))=U := by decide +kernel
 rw [updated] at same
 change energy p U all=energy p U outcomes at same
 change 2≤energy p U all at bound
 omega
#print axioms all_consumed
#print axioms two_of_lt_four
end Owner1007.UpperBudgetParity12
