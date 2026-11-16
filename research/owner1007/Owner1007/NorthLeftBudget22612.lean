import Owner1007.NorthActivation12
namespace Owner1007.NorthLeftBudget22612
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern NetHack.Sokoban.GhostPartition
open Owner1007 Owner1007.TokenAccounting
open Owner1007.NorthActivation12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
def Left : List Cell := PreCage12.U++GS
theorem budget {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤226) :
 energy p Left outcomes≤10 := by
 have total := logged.all_energy p
 have value : p.value FirstSplit12.afterN=211 := by decide +kernel
 have empty : final.holes=[] := completed
 rw [value,empty] at total
 simp only [weightSum] at total
 have perm : (Left++Final222.R).Perm FirstSplit12.afterN.boulders := by decide +kernel
 have same := energy_perm p perm outcomes
 have split := logged.energy_split (by decide +kernel) p Left Final222.R
   (by decide +kernel) (by decide +kernel)
 have whole := NorthWrap12.canonical_north logged
 have right := RightPrice4.right_energy_four whole completed
 have rightSame : energy p Final222.R (.walk 397::.push 371 (.stay 345)::outcomes)=
     energy p Final222.R outcomes :=
   (NorthWrap12.energy_north Final222.R outcomes).trans (congrArg (fun group=>energy p group outcomes)
     (show update Final222.R (.push 371 (.stay 345))=Final222.R by decide +kernel))
 change 4≤energy p Final222.R (.walk 397::.push 371 (.stay 345)::outcomes) at right
 rw [rightSame] at right
 simp only [Int.ofNat_eq_natCast] at total
 omega
#print axioms budget
end Owner1007.NorthLeftBudget22612
