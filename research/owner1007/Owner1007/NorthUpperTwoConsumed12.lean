import Owner1007.North211Tight22812
import Owner1007.TokenCounting
namespace Owner1007.NorthUpperTwoConsumed12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential
abbrev U := PreCage12.U
theorem all_consumed {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (small : energy p U outcomes≤2) :
 ∀ cell∈U, endGroup [cell] outcomes=[] := by
 intro cell member
 apply Classical.byContradiction
 intro alive
 have singleton : [cell]⊆U := by simpa using member
 have upperActual : U⊆FirstSplit12.afterN.boulders := by decide +kernel
 have mono := logged.energy_mono Generated.soko1_2_potential_valid (by decide +kernel)
   [cell] U (by simp) (by decide +kernel) (List.Subset.trans singleton upperActual) upperActual singleton
 change energy p [cell] outcomes≤energy p U outcomes at mono
 have ledger := survivor_energy p cell outcomes alive
 have minDebt : ∀ cell∈U, (8:Int)≤-p.boulder cell := by decide +kernel
 have positive := minDebt cell member
 simp only [Int.ofNat_eq_natCast] at ledger
 have nn := Int.ofNat_nonneg (ownPushes [cell] outcomes)
 omega
theorem end_empty {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (small : energy p U outcomes≤2) : endGroup U outcomes=[] := by
 have bound := logged.end_count_le (by decide +kernel) U (by decide +kernel) (by decide +kernel)
   (fun _=>false) (fun cell member _=>all_consumed logged small cell member)
 have empty : U.filter (fun _=>false)=[] := by decide +kernel
 rw [empty] at bound
 simpa only [List.length_nil,Nat.le_zero_eq,List.length_eq_zero_iff] using bound
#print axioms all_consumed
#print axioms end_empty
end Owner1007.NorthUpperTwoConsumed12
