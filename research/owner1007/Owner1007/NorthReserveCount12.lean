import Owner1007.NorthBound12
import Owner1007.NorthWrap12
import Owner1007.Final222
import Owner1007.RightPrice4
namespace Owner1007.NorthReserveCount12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential

theorem canonical_bound {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (reserve : Nat)
 (lower : Int.ofNat reserve≤energy p NorthBound12.G outcomes) :
 218+reserve≤1+pushes := by
 have whole := NorthWrap12.canonical_north logged
 let all := .walk 397 :: .push 371 (.stay 345) :: outcomes
 have perm : (update Final222.G (.push 371 (.stay 345))).Perm NorthBound12.G := by decide +kernel
 have same : energy p Final222.G all=energy p NorthBound12.G outcomes :=
   (NorthWrap12.energy_north Final222.G outcomes).trans (energy_perm p perm outcomes)
 have canonicalLower : Int.ofNat reserve≤energy p Final222.G all := by rw [same]; exact lower
 have upper := Final222.upper_energy_two whole completed
 change 2≤energy p Final222.U all at upper
 have right := RightPrice4.right_energy_four whole completed
 change 4≤energy p Final222.R all at right
 have other := whole.energy_nonnegative Generated.soko1_2_potential_valid [213]
 change 0≤energy p [213] all at other
 have total := Final222.total_energy whole completed
 change energy p Final222.U all+energy p Final222.G all+energy p [213] all+energy p Final222.R all=
   Int.ofNat (1+pushes)-212 at total
 simp only [Int.ofNat_eq_natCast] at total canonicalLower
 omega
#print axioms canonical_bound
end Owner1007.NorthReserveCount12
