import Owner1007.RightCapacity12
import Owner1007.NorthReserveCount12
namespace Owner1007.NorthGCapacity12
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.HazardPattern
open NetHack.Sokoban.GhostPartition NetHack.Sokoban.GhostProjection
open Owner1007 Owner1007.TokenAccounting
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
abbrev p := Generated.soko1_2Potential

theorem right_small_of_survives {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
 (completed : Goal final) (group : List Cell)
 (unique : (group++Final222.R).Nodup) (subset : group++Final222.R⊆soko1_2.initial.boulders)
 (survives : endGroup group outcomes≠[]) :
 (endGroup Final222.R outcomes).length≤1 := by
 have actualUnique : soko1_2.initial.boulders.Nodup := by decide +kernel
 have split := logged.end_split actualUnique group Final222.R unique subset
 have ends := logged.end_subset actualUnique (group++Final222.R) unique subset
 have size := List.Nodup.length_le_of_subset ends.1 ends.2
 have count := split.length_eq
 simp only [List.length_append] at count
 have positive : 1≤(endGroup group outcomes).length := by
   cases same : endGroup group outcomes with
   | nil => exact False.elim (survives same)
   | cons c rest => simp only [List.length_cons];omega
 have conserved := logged.trace.conservation
 have empty : final.holes=[] := completed
 change 20+final.holes.length=final.boulders.length+18 at conserved
 rw [empty] at conserved
 simp only [List.length_nil] at conserved
 omega

theorem right_five_of_G_survives {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board soko1_2.initial dirs final pushes moves outcomes)
 (completed : Goal final) (survives : endGroup Final222.G outcomes≠[]) :
 5≤energy p Final222.R outcomes := by
 have small := right_small_of_survives logged completed Final222.G (by decide +kernel) (by decide +kernel) survives
 exact RightCapacity12.right_energy_five_of_one p logged (RightPrice4.p_energy_two logged completed)
   (RightCapacity12.q_energy_three_of_one logged) small

theorem canonical_survivor_bound {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final) (lower : 8≤energy p NorthBound12.G outcomes)
 (survives : endGroup NorthBound12.G outcomes≠[]) : 227≤1+pushes := by
 have whole := NorthWrap12.canonical_north logged
 let all := .walk 397::.push 371 (.stay 345)::outcomes
 have perm : (update Final222.G (.push 371 (.stay 345))).Perm NorthBound12.G := by decide +kernel
 have sameG : energy p Final222.G all=energy p NorthBound12.G outcomes :=
   (NorthWrap12.energy_north Final222.G outcomes).trans (energy_perm p perm outcomes)
 have sameEnd := endGroup_perm perm outcomes
 have survivesWhole : endGroup Final222.G all≠[] := by
   intro empty
   change endGroup (update Final222.G (.push 371 (.stay 345))) outcomes=[] at empty
   have count := sameEnd.length_eq
   rw [empty] at count
   simp only [List.length_nil] at count
   have gone : endGroup NorthBound12.G outcomes=[] := List.eq_nil_of_length_eq_zero (by omega)
   exact survives gone
 have right := right_five_of_G_survives whole completed survivesWhole
 change 5≤energy p Final222.R all at right
 have upper := Final222.upper_energy_two whole completed
 change 2≤energy p Final222.U all at upper
 have nnS := whole.energy_nonnegative Generated.soko1_2_potential_valid [213]
 change 0≤energy p [213] all at nnS
 have total := Final222.total_energy whole completed
 change energy p Final222.U all+energy p Final222.G all+energy p [213] all+energy p Final222.R all=
   Int.ofNat (1+pushes)-212 at total
 rw [sameG] at total
 simp only [Int.ofNat_eq_natCast] at total
 omega

theorem canonical_nine_or_survivor {dirs final pushes moves outcomes}
 (logged : Logged soko1_2.board FirstSplit12.afterN dirs final pushes moves outcomes)
 (completed : Goal final)
 (lower : 9≤energy p NorthBound12.G outcomes ∨
   (8≤energy p NorthBound12.G outcomes ∧ endGroup NorthBound12.G outcomes≠[])) :
 227≤1+pushes := by
 rcases lower with nine|⟨eight,survives⟩
 · exact NorthReserveCount12.canonical_bound logged completed 9 nine
 · exact canonical_survivor_bound logged completed eight survives
#print axioms canonical_nine_or_survivor
end Owner1007.NorthGCapacity12
