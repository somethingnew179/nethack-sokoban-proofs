import Owner1007.NorthPrepared12
import Owner1007.NorthReserveCount12
import Owner1007.LoggedAppend11

namespace Owner1007.NorthActivation12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def GS : List Cell := NorthBound12.G++[213]
theorem canonical_joint_bound {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (reserve : Nat)
 (lower : Int.ofNat reserve≤energy p GS outcomes) :
 218+reserve≤1+pushes := by
 have whole := NorthWrap12.canonical_north logged
 let all := .walk 397 :: .push 371 (.stay 345) :: outcomes
 have sameU : energy p Final222.U all=energy p Final222.U outcomes := by
   exact (NorthWrap12.energy_north Final222.U outcomes).trans (congrArg (fun group=>energy p group outcomes)
     (show update Final222.U (.push 371 (.stay 345))=Final222.U by decide +kernel))
 have sameS : energy p [213] all=energy p [213] outcomes := by
   exact (NorthWrap12.energy_north [213] outcomes).trans (congrArg (fun group=>energy p group outcomes)
     (show update [213] (.push 371 (.stay 345))=[213] by decide +kernel))
 have sameR : energy p Final222.R all=energy p Final222.R outcomes := by
   exact (NorthWrap12.energy_north Final222.R outcomes).trans (congrArg (fun group=>energy p group outcomes)
     (show update Final222.R (.push 371 (.stay 345))=Final222.R by decide +kernel))
 have perm : (update Final222.G (.push 371 (.stay 345))).Perm NorthBound12.G := by decide +kernel
 have sameG : energy p Final222.G all=energy p NorthBound12.G outcomes :=
   (NorthWrap12.energy_north Final222.G outcomes).trans (energy_perm p perm outcomes)
 have split := logged.energy_split (by decide +kernel) p NorthBound12.G [213]
   (by decide +kernel) (by decide +kernel)
 change energy p GS outcomes=energy p NorthBound12.G outcomes+energy p [213] outcomes at split
 have total := Final222.total_energy whole completed
 have upper := Final222.upper_energy_two whole completed
 have right := RightPrice4.right_energy_four whole completed
 change 2≤energy p Final222.U all at upper
 change 4≤energy p Final222.R all at right
 change energy p Final222.U all+energy p Final222.G all+energy p [213] all+energy p Final222.R all=
   Int.ofNat (1+pushes)-212 at total
 rw [sameU,sameG,sameS,sameR] at total
 rw [sameU] at upper
 rw [sameR] at right
 simp only [Int.ofNat_eq_natCast] at total lower
 omega

theorem pre_s_heads : ∀ i, ∀ hero∈PreCage12.northRegion i, ∀ dir∈allDirs,
 ∀ source∈([213,212]:List Cell), PreCage12.sPaid source dir →
 advance soko1_2.board hero dir=some source →
 BlockedPush soko1_2.board (PreCage12.northLocks i) source dir ∨
 (source=212 ∧ dir=.west ∧ PreCage12.northS i=212) := by decide +kernel
#print axioms canonical_joint_bound
#print axioms pre_s_heads
#print axioms TokenAccounting.Logged.append
end Owner1007.NorthActivation12
