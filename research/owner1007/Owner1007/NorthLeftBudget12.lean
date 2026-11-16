import Owner1007.NorthBudget22312
import Owner1007.NorthTagFacts12
namespace Owner1007.NorthLeftBudget12
open NetHack.Sokoban NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007.TokenAccounting
abbrev p := Generated.soko1_2Potential
def canonicalLeft : List Cell := Final222.U++(Final222.G++[213])

theorem left_seven {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤223) :
 energy p NorthTagFacts12.selected outcomes≤7 := by
 have whole := NorthWrap12.canonical_north logged
 let all := .walk 397 :: .push 371 (.stay 345) :: outcomes
 have first := whole.energy_split (by decide +kernel) p Final222.U (Final222.G++[213])
   (by decide +kernel) (by decide +kernel)
 change energy p canonicalLeft all = energy p Final222.U all + energy p (Final222.G++[213]) all at first
 have second := whole.energy_split (by decide +kernel) p Final222.G [213] (by decide +kernel) (by decide +kernel)
 change energy p (Final222.G++[213]) all = energy p Final222.G all + energy p [213] all at second
 have total := Final222.total_energy whole completed
 change energy p Final222.U all + energy p Final222.G all + energy p [213] all + energy p Final222.R all =
   Int.ofNat (1+pushes)-212 at total
 have right := RightPrice4.right_energy_four whole completed
 change 4≤energy p Final222.R all at right
 have perm : (update canonicalLeft (.push 371 (.stay 345))).Perm NorthTagFacts12.selected := by decide +kernel
 have same : energy p canonicalLeft all=energy p NorthTagFacts12.selected outcomes :=
   (NorthWrap12.energy_north canonicalLeft outcomes).trans (energy_perm p perm outcomes)
 simp only [Int.ofNat_eq_natCast] at total
 omega
#print axioms left_seven
end Owner1007.NorthLeftBudget12
