import Owner1007.NorthGCapacity12
import Owner1007.NorthLeftBudget22612
namespace Owner1007.NorthLeftSurvival12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential
abbrev Left := NorthLeftBudget22612.Left
def originalLeft : List Cell := Final222.U++Final222.G++[213]
theorem right_five {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (survives : endGroup Left outcomes≠[]) :
 5≤energy p Final222.R outcomes := by
 have whole := NorthWrap12.canonical_north logged
 let all := .walk 397::.push 371 (.stay 345)::outcomes
 have perm : (update originalLeft (.push 371 (.stay 345))).Perm Left := by decide +kernel
 have sameEnd := endGroup_perm perm outcomes
 have survivesWhole : endGroup originalLeft all≠[] := by
   intro empty
   change endGroup (update originalLeft (.push 371 (.stay 345))) outcomes=[] at empty
   have count := sameEnd.length_eq
   rw [empty] at count
   have gone : endGroup Left outcomes=[] := List.eq_nil_of_length_eq_zero (by simpa using count.symm)
   exact survives gone
 have small := NorthGCapacity12.right_small_of_survives whole completed originalLeft
   (by decide +kernel) (by decide +kernel) survivesWhole
 have right := RightCapacity12.right_energy_five_of_one p whole (RightPrice4.p_energy_two whole completed)
   (RightCapacity12.q_energy_three_of_one whole) small
 have rightSame : energy p Final222.R all=energy p Final222.R outcomes :=
   (NorthWrap12.energy_north Final222.R outcomes).trans (congrArg (fun group=>energy p group outcomes)
     (show update Final222.R (.push 371 (.stay 345))=Final222.R by decide +kernel))
 change 5≤energy p Final222.R all at right
 rwa [rightSame] at right

/-- At the tight226 budget, a Left reserve10 exhausts both survivor slots
on the Right. Thus every selected original Left identity must consume. -/
theorem consumed_of_ten {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (cheap : 1+pushes≤226)
 (lower : 10≤energy p Left outcomes) : endGroup Left outcomes=[] := by
 apply Classical.byContradiction
 intro survives
 have right := right_five logged completed survives
 have total := logged.all_energy p
 have value : p.value FirstSplit12.afterN=211 := by decide +kernel
 have empty : final.holes=[] := completed
 rw [value,empty] at total
 simp only [weightSum] at total
 have perm : (Left++Final222.R).Perm FirstSplit12.afterN.boulders := by decide +kernel
 have same := energy_perm p perm outcomes
 have split := logged.energy_split (by decide +kernel) p Left Final222.R
   (by decide +kernel) (by decide +kernel)
 simp only [Int.ofNat_eq_natCast] at total
 omega
#print axioms right_five
#print axioms consumed_of_ten
end Owner1007.NorthLeftSurvival12
